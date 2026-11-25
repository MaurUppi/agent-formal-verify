#!/usr/bin/env python3
# Copyright (c) 2026 Michael Denyer
# SPDX-License-Identifier: GPL-3.0-only
"""Record what each model specifies before agents edit it, and compare it afterwards.

A model's surface is a mapping from item name to a canonical value. Every tool
uses one rule to compare surfaces: a removed item or a changed value is a
change, and so is an added item whose kind narrows what is checked.

  .statements  Lean. The toolchain, and each declaration's kind, type hash and value hash.
               Added declarations are allowed.
  .matrix      TLA+. Each run's effective checks and each reach check's selected inputs,
               and the normalized definitions of Spec,
               of each operator a check or reach line names, and of the operators those
               reference through local EXTENDS. Local INSTANCE substitutions retain their whole module tree.
  .rs          Kani. Each qualified harness name with the #[cfg(...)] attributes other
               than cfg(kani), and the #[cfg_attr(..., cfg(...))] ones, on it, its enclosing
               items, the file and each out-of-line mod declaration that leads to the file from a crate root, through
               #[path], and each kani::assume, kani::any_where, kani::cover! and
               #[kani::stub] with its owning free function, under inline modules. Unsupported owners fail. Added covers and harnesses are allowed.
               Added assumes and stubs are changes.

Usage:
  baseline.py record <record-file> <model-file>...   record these files, keep the other entries
  baseline.py compare <record-file>                  exit 1 when a recorded file changed
  baseline.py move <record-file> <old> <new> [--module OLD NEW]
                                                     compare old's entry with new from now on

Compare prints UNCHANGED or CHANGED per file, indented lines for each item that
changed, and a SUMMARY line. Move prints MOVED; it reads only the record, never
the new file, and with --module renames the recorded Kani owners under module
OLD to sit under NEW. Exit codes: 0 unchanged, 1 changed or a record or model
file that fails to parse, 2 usage error.
"""
import argparse
import bisect
import hashlib
import json
import os
import re
import sys
from pathlib import Path
from typing import NamedTuple

sys.dont_write_bytecode = True

import runner
import tlc
from lean_records import read_record as read_lean_record

FORMAT = 2
NARROWING = {"lean": (), "tla": (), "kani": ("assume", "stub")}
KINDS = {".statements": "lean", ".matrix": "tla", ".rs": "kani"}
STRING = re.compile(r'"(?:\\.|[^"\\])*"', re.DOTALL)


def collapse(text, literals=None):
    if literals is None:
        literals = (match.span() for match in STRING.finditer(text))
    parts, end = [], 0
    for start, stop in literals:
        parts.extend((re.sub(r"\s+", " ", text[end:start]), text[start:stop]))
        end = stop
    parts.append(re.sub(r"\s+", " ", text[end:]))
    return "".join(parts).strip()


class Surface(dict):
    def add(self, name, value=""):
        candidate, count = name, 1
        while candidate in self:
            count += 1
            candidate = f"{name} #{count}"
        self[candidate] = value
        return candidate


def lean_surface(path):
    record = read_lean_record(path)
    surface = Surface()
    surface.add("toolchain", record["toolchain"])
    for entry in record["declarations"]:
        surface.add(f"declaration {entry['name']}", f"{entry['kind']} {entry['typeHash']} {entry['valueHash'] or '-'}")
    return surface


def tla_text(text):
    """Columns can group TLA+ conjunctions and disjunctions across lines."""
    lines = [line.rstrip() for line in text.splitlines() if line.strip()]
    return "\n".join(lines) if len(lines) > 1 else collapse("".join(lines))


def blank_tla_comments(text):
    out, i = [], 0
    while i < len(text):
        if text[i] == '"':
            string = STRING.match(text, i)
            if string is None:
                raise ValueError("unterminated TLA+ string")
            out.append(string[0])
            i = string.end()
        elif text.startswith("(*", i):
            start, depth = i, 0
            while i < len(text):
                if text.startswith("(*", i):
                    depth += 1
                    i += 2
                elif text.startswith("*)", i):
                    depth -= 1
                    i += 2
                    if not depth:
                        break
                else:
                    i += 1
            # A following token keeps its source column, even after a nested comment.
            out.append(re.sub(r"[^\s]", " ", text[start:i]))
        elif text.startswith("\\*", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
            out.append(" ")
        else:
            out.append(text[i])
            i += 1
    return "".join(out)


DEFINITION = re.compile(r"(?:LOCAL\s+)?(\w*[A-Za-z]\w*)\s*(?:\((?:[^()]|\([^()]*\))*\)|\[(?:[^\[\]]|\[[^\[\]]*\])*\])?\s*==")
MODULE_LEVEL = re.compile(r"-{4,}|={4,}|(?:EXTENDS|VARIABLES?|CONSTANTS?|ASSUME|ASSUMPTION|AXIOM|THEOREM|LEMMA|PROPOSITION|COROLLARY|INSTANCE|RECURSIVE|USE|HIDE)\b")
IDENTIFIER = re.compile(r"\w*[A-Za-z]\w*")
SUBSCRIPT = r"_(\w+|<<[^>]*>>)"
SPEC_ACTIONS = re.compile(rf"\[\]\[[^\]]*\]{SUBSCRIPT}|[WS]F{SUBSCRIPT}\s*\([^()]*\)")
# The prefix that joins a subscript, such as vars in WF_vars, [A]_vars or <<A>>_vars, to one token.
SUBSCRIPT_PREFIX = re.compile(r"\b[WS]F_|\]_|>>_")


def begins_in_column_zero(line):
    return line[:1].strip() != ""


DEFINITION_TOKENS = re.compile(r"\b(?:LET|IN)\b|(?<!=)==(?!=)")


def has_unplaced_definition(code):
    """Return whether a definition can lie outside the column-0 headers that tla_definitions splits on.

    An indented `==` inside an open LET defines a LET-local operator. Any other indented `==`, a line
    that starts with `==`, or a column-0 header while a LET is open can define a module operator.
    """
    open_lets = 0
    for line in code.split("\n"):
        indented = not begins_in_column_zero(line)
        if open_lets and not indented and ("==" in line or MODULE_LEVEL.match(line)):
            return True
        for token in DEFINITION_TOKENS.finditer(line):
            if token[0] == "LET":
                open_lets += 1
            elif token[0] == "IN":
                open_lets = max(open_lets - 1, 0)
            elif not open_lets and (indented or token.start() == 0):
                return True
    return False


def tla_definitions(text):
    found, unreadable, name, lines = {}, set(), None, []
    for line in text.split("\n"):
        if begins_in_column_zero(line):
            match = DEFINITION.match(line)
            header = None if match or MODULE_LEVEL.match(line) or "==" not in line else collapse(line.partition("==")[0])
            if match or header or MODULE_LEVEL.match(line):
                if name:
                    found[name] = tla_text("\n".join(lines))
                name, lines = (match[1] if match else header), ([line] if match or header else [])
                if header:
                    unreadable.add(header)
                continue
        if name:
            lines.append(line)
    if name:
        found[name] = tla_text("\n".join(lines))
    return found, unreadable


EXTENDS = re.compile(r"\bEXTENDS\s+(\w+(?:\s*,\s*\w+)*)")
INSTANCE = re.compile(r"\bINSTANCE\s+(\w+)")
INDENTED_DEFINITION = re.compile(r"^[ \t]*" + DEFINITION.pattern, re.MULTILINE)


def tla_module_surface(directory, spec, operators):
    """Resolve operator references in the module that defines them, including sibling imports."""
    root = Path(spec)
    texts, bodies, scopes, exports = {}, {}, {}, {}
    required, visiting = set(), set()
    whole_modules = False

    def load(path):
        nonlocal whole_modules
        if path in exports:
            return exports[path]
        if path in visiting:
            raise ValueError(f"cyclic TLA+ import at {path}")
        visiting.add(path)
        text = blank_tla_comments(tlc.read_raw(directory / path))
        texts[path] = text
        code = STRING.sub('""', text)
        if has_unplaced_definition(code):
            whole_modules = True
        scope = {}
        for group in EXTENDS.findall(code):
            for name in IDENTIFIER.findall(group):
                sibling = path.with_name(f"{name}.tla")
                if (directory / sibling).is_file():
                    scope.update(load(sibling))
        for name in INSTANCE.findall(code):
            sibling = path.with_name(f"{name}.tla")
            if (directory / sibling).is_file():
                whole_modules = True
                load(sibling)
        definitions, unreadable = tla_definitions(text)
        for name, body in definitions.items():
            key = (path, name)
            bodies[key] = body
            scope[name] = key
        required.update((path, name) for name in unreadable)
        scopes[path] = scope
        exports[path] = {name: key for name, key in scope.items() if not re.match(r"LOCAL\s", bodies[key])}
        visiting.remove(path)
        return exports[path]

    load(root)
    surface = {f"imports {spec}": sorted(str(path) for path in texts if path != root)}
    fallback_names = set()
    if whole_modules:
        fallback_names = {match[1] for text in texts.values() for match in INDENTED_DEFINITION.finditer(text)}
    for name in sorted({"Spec", *operators}):
        if name in scopes[root]:
            required.add(scopes[root][name])
        elif name.rpartition("!")[2] not in fallback_names:
            raise ValueError(f"{name} is named in the {spec} section but no definition was found in it or its local imports")
    if whole_modules:
        # Preserve substitutions and dependencies whose operator scope cannot be resolved.
        for path, text in texts.items():
            surface[f"module text {spec} | {path}"] = tla_text(text)
        return surface

    seen = set()
    while required:
        key = required.pop()
        if key in seen:
            continue
        seen.add(key)
        owner, name = key
        surface[f"definition {owner} {name}"] = bodies[key]
        header, _, body = bodies[key].partition("==")
        body = STRING.sub('""', body)
        if key == scopes[root]["Spec"]:
            # Keep the subscript, such as vars: it decides which steps may stutter and what fairness requires.
            body = SPEC_ACTIONS.sub(lambda form: f" {form[1] or form[2]} ", body)
        body = SUBSCRIPT_PREFIX.sub(" ", body)
        if "[" in header:
            # A function definition such as F[x \in S] == ... references S in its header.
            body = f"{header} {body}"
        required.update(scopes[owner][word] for word in IDENTIFIER.findall(body) if word in scopes[owner])
    return surface


def tla_surface(path):
    surface = Surface()
    surface.add("TLA+ layout version", 1)
    specs = {}
    plan = tlc.MatrixPlan(path)
    tasks = plan.checked_tasks()
    for spec in plan.specs:
        surface.add(f"spec {spec}")
        specs.setdefault(spec, set())
    for task in tasks:
        if task.reach:
            surface.add(f"reach {task.spec} {task.reach.operator} | {collapse(task.reach.match)}",
                        {"run": collapse(task.run.label), "constants": collapse(task.run.constants)})
            specs[task.spec].add(task.reach.operator)
        else:
            run = surface.add(f"run {task.spec} {collapse(task.run.label)}", collapse(task.run.constants))
            for check in task.checks:
                for name in check.names:
                    surface.add(f"check {task.spec} {check.kind} {name} | [{run}]")
                specs[task.spec].update(check.names)
    for spec, operators in specs.items():
        source = path.parent / spec
        if not source.is_file():
            raise ValueError(f"{path}: spec {spec} not found")
        surface.update(tla_module_surface(path.parent, spec, operators))
    return surface


class RustSource(NamedTuple):
    uncommented: str
    without_comments_or_strings: str
    literals: list


def rust_masks(source):
    text, mask = list(source), list(source)
    literals = []

    def blank(start, end, *, both):
        for i in range(start, end):
            if source[i] != "\n":
                mask[i] = " "
                if both:
                    text[i] = " "

    i = 0
    while i < len(source):
        if source.startswith("//", i):
            end = source.find("\n", i)
            end = len(source) if end < 0 else end
            blank(i, end, both=True)
            i = end
        elif source.startswith("/*", i):
            depth, start = 0, i
            while i < len(source):
                if source.startswith("/*", i):
                    depth, i = depth + 1, i + 2
                elif source.startswith("*/", i):
                    depth, i = depth - 1, i + 2
                    if not depth:
                        break
                else:
                    i += 1
            blank(start, i, both=True)
        elif raw := re.compile(r'(?<!\w)[bc]?r(#*)"').match(source, i):
            close = source.find('"' + raw[1], raw.end())
            content_end = len(source) if close < 0 else close
            blank(raw.end(), content_end, both=False)
            i = content_end + 1 + len(raw[1])
            literals.append((raw.start(), min(i, len(source))))
        elif source[i] == '"':
            opening = i
            start = i = i + 1
            while i < len(source) and source[i] != '"':
                i += 2 if source[i] == "\\" else 1
            blank(start, min(i, len(source)), both=False)
            i += 1
            literals.append((opening, min(i, len(source))))
        elif char := re.compile(r"'(?:\\.[^']*|[^'\\])'").match(source, i):
            blank(char.start() + 1, char.end() - 1, both=False)
            i = char.end()
            literals.append(char.span())
        else:
            i += 1
    return RustSource("".join(text), "".join(mask), literals)


def after_closing(mask, opener):
    closer = {"(": ")", "[": "]", "{": "}"}[mask[opener]]
    depth = 0
    for i in range(opener, len(mask)):
        depth += (mask[i] == mask[opener]) - (mask[i] == closer)
        if not depth:
            return i + 1
    raise ValueError(f"unbalanced {mask[opener]} at offset {opener}")


class RustFunction(NamedTuple):
    name: str
    start: int
    keyword: int
    body: int
    end: int


RUST_ITEM = re.compile(r"\b(fn|mod)\s+((?:r#)?\w+)\b")
INCLUDE = re.compile(r"\binclude\s*!$")


def rust_functions(mask):
    """Locate free functions, inline modules, out-of-line `mod name;` declarations and `include!(...)` items outside
    function bodies; leave macro and other item bodies opaque.

    A declaration's or an include's body is its `;`.
    """
    functions, modules, opaque, declarations, includes, counts = [], [], [], [], [], {}

    def add_include(boundary, header, stop, in_function):
        if not in_function and (include := INCLUDE.search(header)):
            semicolon = re.compile(r"\s*;").match(mask, stop)
            includes.append(RustFunction("include", boundary, boundary + include.start(), semicolon.end() - 1 if semicolon else stop - 1, stop))

    def walk(start, end, namespace=(), in_function=False):
        i, boundary, item = start, start, None
        while i < end:
            if match := RUST_ITEM.match(mask, i):
                item = (match[1], match[2], match.start())
                i = match.end()
            elif mask[i] in "([":
                stop = after_closing(mask, i)
                header = mask[boundary:i].rstrip()
                if header.endswith("!"):
                    opaque.append((i, stop))
                    add_include(boundary, header, stop, in_function)
                i = stop
            elif mask[i] == "{":
                stop = after_closing(mask, i)
                header = mask[boundary:i].rstrip()
                macro = header.endswith("!") or bool(re.search(r"\bmacro_rules\s*!\s*\w+\s*$", header))
                if item and not macro:
                    kind, name, keyword = item
                    qualified = (*namespace, name)
                    if kind == "fn":
                        owner = "::".join(qualified)
                        counts[owner] = counts.get(owner, 0) + 1
                        suffix = f"[{counts[owner]}]" if counts[owner] > 1 else ""
                        functions.append(RustFunction(owner + suffix, boundary, keyword, i, stop))
                    else:
                        modules.append(RustFunction("::".join(qualified), boundary, keyword, i, stop))
                    walk(i + 1, stop - 1, qualified, kind == "fn")
                elif in_function and not macro and not re.search(r"\b(?:impl|trait|struct|enum|union|extern|macro)\b", header):
                    walk(i + 1, stop - 1, namespace, True)
                else:
                    opaque.append((i, stop))
                    add_include(boundary, header, stop, in_function)
                i = boundary = stop
                item = None
            else:
                if mask[i] == ";":
                    if item and item[0] == "mod" and not in_function:
                        declarations.append(RustFunction("::".join((*namespace, item[1])), boundary, item[2], i, i + 1))
                    boundary, item = i + 1, None
                i += 1

    walk(0, len(mask))
    return functions, modules, opaque, declarations, includes


KANI_ATTRIBUTE = r"#\s*\[\s*(?:cfg_attr\s*\(\s*kani\s*,\s*)?kani\s*::\s*"
MACROS = (
    ("assume", re.compile(r"\bkani\s*::\s*assume\s*\(")),
    ("assume", re.compile(r"\bkani\s*::\s*any_where\s*(?:::\s*<[^<>]*(?:<[^<>]*>[^<>]*)*>\s*)?\(")),
    ("cover", re.compile(r"\bkani\s*::\s*cover\s*!\s*\(")),
    ("stub", re.compile(KANI_ATTRIBUTE + r"stub\s*\(")),
)
PROOF = re.compile(KANI_ATTRIBUTE + r"proof(?:_for_contract\s*\([^)]*\))?\s*\)?\s*\]")
KANI_TOKEN = re.compile(r"\bkani\s*::\s*(?:assume|any_where|cover|stub|proof)\w*\b")
ATTRIBUTE = re.compile(r"#\s*(!\s*)?\[")
INNER_ATTRIBUTE = re.compile(r"[\s\ufeff]*#\s*!\s*\[")
RENAMING_IMPORT = re.compile(r"\buse\s+[^;]*?(?<![\w:])(?:::\s*)?kani\b[^;]*?(?:\bas\b|\*|\b(?:assume|any_where|cover|stub|proof)\w*\b)|\bextern\s+crate\s+kani\s+as\b")


def applies_cfg(attribute):
    """Return whether a compact `cfg_attr(predicate, attribute, ...)` applies a cfg or a module path in its own
    attribute list."""
    arguments, depth, start = [], 0, len("cfg_attr(")
    for i in range(start, len(attribute) - 1):
        depth += (attribute[i] in "([{") - (attribute[i] in ")]}")
        if attribute[i] == "," and not depth:
            arguments.append(attribute[start:i])
            start = i + 1
    arguments.append(attribute[start:-1])
    return any(argument.startswith(("cfg(", "path=")) or argument.startswith("cfg_attr(") and applies_cfg(argument) for argument in arguments[1:])


def outer_attributes(source, start, keyword):
    """Yield the contents of each top-level outer attribute between start and keyword; skip inner attributes."""
    mask = source.without_comments_or_strings
    while attribute := ATTRIBUTE.search(mask, start, keyword):
        opener = attribute.end() - 1
        start = after_closing(mask, opener)
        if not attribute[1]:
            yield rust_masks(source.uncommented[opener + 1:start - 1])


def cfg_guards(source, items):
    """Return the cfg attributes other than cfg(kani), and the cfg_attr ones whose attribute list applies a cfg or a
    module path, on each (start, keyword, body) item, between its start and its fn or mod keyword, and at the start
    of its body.

    A body of -1 stands for the file, which has only inner attributes, and a body at a `;` for an out-of-line `mod`
    declaration, which has none. An attribute nested inside another attribute's tokens is not read.
    """
    text, mask = source.uncommented, source.without_comments_or_strings
    guards = []

    def read(attribute):
        compact = re.sub(r"\s+", "", attribute.without_comments_or_strings)
        if compact.startswith("cfg(") and compact != "cfg(kani)" or compact.startswith("cfg_attr(") and applies_cfg(compact):
            guards.append(collapse(attribute.uncommented, attribute.literals))

    for start, keyword, body in items:
        if body >= 0:
            for attribute in outer_attributes(source, start, keyword):
                read(attribute)
        if body >= 0 and mask[body] == ";":
            continue
        inner = body + 1
        while attribute := INNER_ATTRIBUTE.match(mask, inner):
            opener = attribute.end() - 1
            inner = after_closing(mask, opener)
            read(rust_masks(text[opener + 1:inner - 1]))
    return " ".join(guards)


PATH_ATTRIBUTE = re.compile(r"\bpath\s*=\s*")


def module_paths(source, item, file):
    """Return the paths that `#[path = "..."]` sets on a module item, and those that a cfg_attr may set."""
    paths, conditional = [], []
    for attribute in outer_attributes(source, item.start, item.keyword):
        compact = re.sub(r"\s+", "", attribute.without_comments_or_strings)
        if not compact.startswith(("path=", "cfg_attr(")):
            continue
        for setting in PATH_ATTRIBUTE.finditer(attribute.without_comments_or_strings):
            value = string_value(next((attribute.uncommented[begin:end] for begin, end in attribute.literals if begin == setting.end()), ""))
            if value is None:
                line = source.without_comments_or_strings.count("\n", 0, item.start) + 1
                raise ValueError(f"{file}:{line}: cannot read the path in '{collapse(attribute.uncommented, attribute.literals)}'; write it as a string without escapes")
            (paths if compact.startswith("path=") else conditional).append(value)
    return paths, conditional


def string_value(literal):
    """Return the value of a Rust string literal without escapes, or None."""
    plain = re.fullmatch(r'r(#*)"(.*)"\1', literal, re.DOTALL) or re.fullmatch(r'"([^"\\]*)"', literal)
    return plain[plain.lastindex] if plain else None


class RustFile(NamedTuple):
    source: RustSource
    functions: list
    modules: list
    opaque: list
    declarations: list
    includes: list


PARSED = {}


def parse_rust(path):
    if path not in PARSED:
        source = rust_masks(path.read_text(encoding="utf-8"))
        PARSED[path] = RustFile(source, *rust_functions(source.without_comments_or_strings))
    return PARSED[path]


def enclosing_modules(parsed, item):
    return sorted((module for module in parsed.modules if module.start <= item.start < module.end), key=lambda module: module.start)


def module_files(file, owner, parsed, declaration, inner=()):
    """Yield each file that an out-of-line `mod` declaration in file may load, by rustc's rules, and whether that
    file owns its directory, as a crate root, a mod.rs or a `#[path]` file does. inner holds the inline modules
    around the declaration inside a macro body, outermost first."""
    states = [(file.parent, file.parent if owner else file.parent / file.stem)]
    for module in enclosing_modules(parsed, declaration) + list(inner):
        paths, conditional = module_paths(parsed.source, module, file)
        name = module.name.rsplit("::", 1)[-1].removeprefix("r#")
        states = [(child, child) for directory, prefix in states for child in ([] if paths else [prefix / name]) + [directory / path for path in paths + conditional]]
    paths, conditional = module_paths(parsed.source, declaration, file)
    name = declaration.name.rsplit("::", 1)[-1].removeprefix("r#")
    for directory, prefix in states:
        if not paths:
            yield prefix / f"{name}.rs", False
            yield prefix / name / "mod.rs", True
        for path in paths + conditional:
            yield directory / path, True


def crate_roots(path):
    """Return the crate roots whose module trees may hold path, and those of them that Cargo names, or None for a
    file in no crate.

    They are the lib.rs and main.rs in the nearest directory above path that holds either and, in the Cargo package
    of the nearest directory above path with a Cargo.toml, Cargo's target files and each `.rs` path that Cargo.toml
    names.
    """
    marker = next((folder for folder in path.parents if (folder / "lib.rs").is_file() or (folder / "main.rs").is_file()), None)
    package = next((folder for folder in path.parents if (folder / "Cargo.toml").is_file()), None)
    if marker is None and package is None:
        return None
    markers = [marker / "lib.rs", marker / "main.rs"] if marker else []
    named = []
    if package:
        named += [package / "src/lib.rs", package / "src/main.rs"]
        for folder in ("src/bin", "tests", "examples", "benches"):
            named += sorted((package / folder).glob("*.rs")) + sorted((package / folder).glob("*/main.rs"))
        manifest = (package / "Cargo.toml").read_text(encoding="utf-8")
        named += [package / file for file in re.findall(r"""\bpath\s*=\s*["']([^"']+\.rs)["']""", manifest)]
    return tuple(dict.fromkeys(root.resolve() for root in markers + named if root.is_file())), {root.resolve() for root in named}


CONCAT = re.compile(r"(?:\w+\s*::\s*)*concat\s*!\s*[(\[{]")
MANIFEST_DIR = re.compile(r'(?:\w+\s*::\s*)*env\s*!\s*[(\[{]\s*"CARGO_MANIFEST_DIR"\s*,?\s*[)\]}]')


def include_path(argument, file, package):
    """Return the file that the argument of an `include!` in file names, or None when the argument is neither a
    string without escapes nor a `concat!` of such strings and `env!("CARGO_MANIFEST_DIR")`, which is package,
    the directory of the Cargo.toml of the crate being compiled.

    Raises:
        ValueError: The argument uses `env!("CARGO_MANIFEST_DIR")` and package is None.
    """
    argument = argument.strip()
    if (value := string_value(argument)) is not None:
        return file.parent / value
    mask = rust_masks(argument).without_comments_or_strings
    if not (concat := CONCAT.match(mask)) or after_closing(mask, concat.end() - 1) != len(mask):
        return None
    parts, start, depth = [], concat.end(), 0
    for i in range(start, len(mask) - 1):
        depth += (mask[i] in "([{") - (mask[i] in ")]}")
        if mask[i] == "," and not depth:
            parts.append(argument[start:i].strip())
            start = i + 1
    parts.append(argument[start:-1].strip())
    pieces = []
    for part in filter(None, parts):
        if (value := string_value(part)) is not None:
            pieces.append(value)
        elif MANIFEST_DIR.fullmatch(part):
            if package is None:
                raise ValueError('no Cargo.toml above the crate root sets env!("CARGO_MANIFEST_DIR"), so the record cannot tell which file it reads')
            pieces.append(str(package))
        else:
            return None
    return file.parent / "".join(pieces)


TREES = {}


def module_tree(roots):
    """Return the module declarations that lead to each file the crate roots reach, as {file: {(declarer,
    declaration)}}, the (message, text) of each reached file or declaration that could not be read, and the
    package directory of the first crate root that reaches each file, or None outside a Cargo package.

    An `include!("...")` item outside function bodies leads to the file it names, relative to the including file,
    which declares modules as a file that owns its directory does, whatever inline modules hold the include.
    """
    if roots not in TREES:
        edges, broken, seen, packages = {}, [], set(), {}
        work = [(root, True, next((folder for folder in root.parents if (folder / "Cargo.toml").is_file()), None)) for root in roots]
        while work:
            file, owner, package = work.pop()
            if (file, owner, package) in seen:
                continue
            seen.add((file, owner, package))
            packages.setdefault(file, package)
            try:
                parsed = parse_rust(file)
            except ValueError as error:
                broken.append((f"{file}: {error}", file.read_text(encoding="utf-8", errors="replace")))
                continue
            for declaration in parsed.declarations:
                try:
                    targets = list(module_files(file, owner, parsed, declaration))
                except ValueError as error:
                    broken.append((str(error), parsed.source.uncommented[declaration.start:declaration.end]))
                    continue
                for target, owns in targets:
                    if target.is_file():
                        target = target.resolve()
                        edges.setdefault(target, set()).add((file, declaration))
                        work.append((target, owns, package))
            for include in parsed.includes:
                invocation = rust_masks(parsed.source.uncommented[include.keyword:include.end])
                line = parsed.source.without_comments_or_strings.count("\n", 0, include.keyword) + 1
                shown = collapse(invocation.uncommented, invocation.literals)
                try:
                    target = include_path(invocation.uncommented[invocation.without_comments_or_strings.index("!") + 1:].strip()[1:-1], file, package)
                except ValueError as error:
                    broken.append((f"{file}:{line}: cannot read the path in '{shown}': {error}", None))
                    continue
                if target is None:
                    broken.append((f"{file}:{line}: cannot read the path in '{shown}'; write it as a string without escapes, or as concat! of such strings and env!(\"CARGO_MANIFEST_DIR\")", invocation.uncommented))
                elif target.is_file():
                    target = target.resolve()
                    edges.setdefault(target, set()).add((file, include))
                    work.append((target, True, package))
        TREES[roots] = edges, broken, packages
    return TREES[roots]


HIDDEN_DECLARATION = re.compile(r"\bmod\s+(?:r#)?(\w+)\s*;")
HIDDEN_PATH = re.compile(r"[\[,]\s*path\s*=\s*")
HIDDEN_MODULE = re.compile(r"\bmod\s+((?:r#)?\w+)\s*\{")
INVOKED = re.compile(r"(?P<path>(?:::\s*)?(?:\w+\s*::\s*)*)(?P<name>\w+)\s*!\s*$")
LOCAL_PATH = re.compile(r"(?:(?:crate|self|super)\s*::\s*(?:\w+\s*::\s*)*)?")
DEFINED = re.compile(r"\bmacro_rules\s*!\s*(\w+)\s*$")
ITEM_INVOCATION = re.compile(r"(?:\$(?=crate\b))?(?P<path>(?:::\s*)?(?:\w+\s*::\s*)*)(?P<name>\w+)\s*!\s*[(\[{]")
INLINE_MODULE = re.compile(r"\bmod\s+\$?\w+\s*$")
TOKEN = re.compile(r"\$?\w+|.", re.DOTALL)
OPENER = re.compile(r"[(\[{]")
ARM = re.compile(r"\s*=>\s*[(\[{]")
NAME_FRAGMENT = re.compile(r"\$(\w+)\s*:\s*(?:ident|tt)\b")
INCLUDES = ("include", "include_str", "include_bytes")
INCLUDE_CALL = re.compile(r"\binclude\s*!\s*[(\[{]")
HIDDEN = "a module declaration inside a macro or function body may load"
BUILT = "a macro invocation may build a module declaration that loads"
UNREAD = "an invocation of a macro that the record cannot read may build a module declaration that loads"
INCLUDED = "an include! inside a macro or function body reads a file that may load"


def module_builders(parsed):
    """Return the names of the `macro_rules!` macros in a parsed file whose bodies declare `mod $name;`."""
    mask = parsed.source.without_comments_or_strings
    return {defined[1] for start, end in parsed.opaque if (defined := DEFINED.search(mask, max(0, start - 100), start)) and re.search(r"\bmod\s+\$\w+\s*;", mask[start:end])}


def transcribers(mask, start, end):
    """Yield the names of the `ident` and `tt` metavariables of each arm of the `macro_rules!` body mask[start:end],
    with the start and end of the tokens inside the arm's transcriber."""
    i = start
    while (matcher := OPENER.search(mask, i, end)) and (arrow := ARM.match(mask, after_closing(mask, matcher.start()))):
        close = after_closing(mask, arrow.end() - 1)
        yield set(NAME_FRAGMENT.findall(mask, matcher.start(), arrow.start())), arrow.end(), close - 1
        i = close


def item_invocations(mask, start, end, macros, visible):
    """Yield the match of each macro invocation at an item position in mask[start:end], with the tokens inside its
    delimiters: one that starts the tokens or follows a `;`, a `}` or an attribute, and that braces delimit or a `;`
    follows. So does one inside a `$(...)` repetition, a `mod name {...}` body or an invocation there of one of the
    macros that `readable` takes the visible names to reach, but not one inside another group, such as a block or a
    function body."""
    i, item = start, True
    while i < end:
        if mask[i].isspace():
            i += 1
        elif item and (invocation := ITEM_INVOCATION.match(mask, i, end)):
            close = after_closing(mask, invocation.end() - 1)
            braced = mask[invocation.end() - 1] == "{"
            if braced or mask[close:end].lstrip().startswith(";"):
                yield invocation, mask[invocation.end():close - 1]
                if readable(invocation, macros, visible):
                    yield from item_invocations(mask, invocation.end(), close - 1, macros, visible)
            i, item = close, braced
        elif attribute := ATTRIBUTE.match(mask, i, end):
            i = after_closing(mask, attribute.end() - 1)
        elif mask.startswith("$(", i):
            close = after_closing(mask, i + 1)
            yield from item_invocations(mask, i + 2, close - 1, macros, visible)
            i, item = close, True
        elif mask[i] in "([{":
            close = after_closing(mask, i)
            if mask[i] == "{" and INLINE_MODULE.search(mask, start, i):
                yield from item_invocations(mask, i + 1, close - 1, macros, visible)
            i, item = close, mask[i] == "{"
        else:
            item = mask[i] == ";" or item and mask[i] in "*+?"
            i = TOKEN.match(mask, i).end()


class Macros(NamedTuple):
    """The `macro_rules!` definitions in the reached files, each map from a macro's name to the (file, offset) keys
    of its definitions: every definition, and those whose invocations the record can read."""
    every: dict
    readable: dict


def readable(invoked, macros, visible):
    """Return whether an invocation calls a macro that the record can read: one that a path inside the crate names,
    or a bare name, and every definition of the name that the invocation may reach is readable.

    A path reaches every definition of the name, and a bare name those in visible, which maps a name to the keys of
    its definitions in scope at the invocation.
    """
    name = invoked["name"]
    if not LOCAL_PATH.fullmatch(invoked["path"]):
        return False
    found = (macros.every if invoked["path"] else visible).get(name)
    return bool(found) and found <= macros.readable.get(name, set())


def macro_definitions(parsed):
    """Yield the start and end of the body of each `macro_rules!` macro defined in a parsed file, with its name."""
    mask = parsed.source.without_comments_or_strings
    for start, end in parsed.opaque:
        if defined := DEFINED.search(mask, max(0, start - 100), start):
            yield start, end, defined[1]


def readable_macros(parsed_files, builders):
    """Return the `macro_rules!` definitions in the parsed files and those whose invocations the record can read:
    those whose transcribers pass no `ident` or `tt` metavariable of their arm to an invocation at an item position
    of one of the builders or of a macro that the record cannot read. A bare name in a transcriber resolves where
    the macro is invoked, so it may reach every definition of the name."""
    bodies = [(parsed.source.without_comments_or_strings, start, end, name, (file, start)) for file, parsed in parsed_files for start, end, name in macro_definitions(parsed)]
    every = {}
    for *_, name, key in bodies:
        every.setdefault(name, set()).add(key)
    macros = Macros(every, {name: set(keys) for name, keys in every.items()})
    while forwarding := {(name, key) for mask, start, end, name, key in bodies if key in macros.readable[name] and any(
            (invocation["name"] in builders or not readable(invocation, macros, every)) and passes_name(tokens, rf"\$(?:{'|'.join(variables)})\b")
            for variables, begin, stop in transcribers(mask, start + 1, end - 1) if variables
            for invocation, tokens in item_invocations(mask, begin, stop, macros, every))}:
        for name, key in forwarding:
            macros.readable[name].discard(key)
    return macros


def inner_attributes(source, start):
    """Yield the contents of each inner attribute at offset start of source."""
    mask = source.without_comments_or_strings
    while attribute := INNER_ATTRIBUTE.match(mask, start):
        opener = attribute.end() - 1
        start = after_closing(mask, opener)
        yield rust_masks(source.uncommented[opener + 1:start - 1])


def macro_use(attributes):
    """Return whether one of the attributes is `macro_use`."""
    return any(re.sub(r"\s+", "", attribute.without_comments_or_strings) == "macro_use" for attribute in attributes)


def merged(*scopes):
    """Return the union of maps from a macro's name to the keys of its definitions."""
    union = {}
    for names in scopes:
        for name, keys in names.items():
            union.setdefault(name, set()).update(keys)
    return union


IMPORT = re.compile(r"\buse\s+(?:::\s*)?(\$?\w+)\b[^;]*;")
MACRO_EXPORT = re.compile(r"#\s*\[\s*macro_export\b[^\]]*\]\s*(?:#\s*(?:!\s*)?\[[^\]]*\]\s*)*macro_rules\s*!\s*\w+\s*$")


def textual_scopes(roots, edges):
    """Return a function of a reached file and an offset in it that gives the `macro_rules!` macros a bare name may
    reach there, as a map from each name to the (file, offset) keys of its definitions.

    Those are the macros defined earlier in the file, those in scope at every declaration or `include!` that leads
    to the file from a crate root, and those that an earlier `include!` or `#[macro_use]` module declaration brings
    in. A definition or declaration inside an inline module counts outside the module only when the module carries
    `#[macro_use]` or `#![macro_use]`, and one inside a function body only in that body. A `use` item whose path
    starts with `crate`, `self`, `super` or a module that the file declares brings in each definition of the names
    it holds, in the module that holds the item. A `#[macro_export]` macro is visible at the top of a crate root.
    """
    children, inherited, active, definitions, exported, root_scope, known = {}, {}, set(), {}, {}, {}, {}
    for target, routes in edges.items():
        for declarer, declaration in routes:
            children.setdefault(declarer, []).append((declaration, target))
    for file in set(roots) | edges.keys():
        try:
            parsed = parse_rust(file)
        except ValueError:
            continue
        mask = parsed.source.without_comments_or_strings
        for start, _, name in macro_definitions(parsed):
            definitions.setdefault(name, set()).add((file, start))
            if MACRO_EXPORT.search(mask, max(0, start - 300), start):
                root_scope.setdefault(name, set()).add((file, start))

    def escapes(parsed, module):
        return macro_use(outer_attributes(parsed.source, module.start, module.keyword)) or macro_use(inner_attributes(parsed.source, module.body + 1))

    def within(parsed, position, offset, *, leaving=True):
        return all(module.start <= offset < module.end or leaving and escapes(parsed, module) for module in parsed.modules if module.start <= position < module.end) and all(
            function.body <= offset < function.end for function in parsed.functions if function.body <= position < function.end)

    def loads_macros(parsed, declaration, child):
        if parsed.source.without_comments_or_strings.startswith("include", declaration.keyword) or macro_use(outer_attributes(parsed.source, declaration.start, declaration.keyword)):
            return True
        try:
            return macro_use(inner_attributes(parse_rust(child).source, 0))
        except ValueError:
            return False

    def facts(file):
        if file not in known:
            parsed = parse_rust(file)
            mask = parsed.source.without_comments_or_strings
            modules = {"crate", "$crate", "self", "super"} | {item.name.rsplit("::", 1)[-1].removeprefix("r#") for item in parsed.declarations + parsed.modules}
            imports = [(use.start(), words) for use in IMPORT.finditer(mask) if use[1] in modules and (words := [word for word in re.findall(r"\w+", use[0]) if word in definitions])]
            known[file] = parsed, [(start, name) for start, _, name in macro_definitions(parsed)], imports
        return known[file]

    def local(file, offset, seen):
        try:
            parsed, defined, imports = facts(file)
        except ValueError:
            return {}
        names = merged(*({name: {(file, start)}} for start, name in defined if start < offset and within(parsed, start, offset)))
        names = merged(names, *({word: definitions[word]} for start, words in imports if within(parsed, start, offset, leaving=False) for word in words))
        if file in roots and not any(module.start <= offset < module.end for module in parsed.modules):
            names = merged(names, root_scope)
        for declaration, child in children.get(file, ()):
            if child not in seen and declaration.start < offset and within(parsed, declaration.start, offset) and loads_macros(parsed, declaration, child):
                if child not in exported:
                    exported[child] = local(child, float("inf"), seen | {child})
                names = merged(names, exported[child])
        return names

    def scope(file, offset):
        if file not in inherited:
            if file in active:
                return local(file, offset, {file})
            active.add(file)
            routes = [scope(declarer, declaration.start) for declarer, declaration in edges.get(file, ())] if file not in roots else []
            common = set.intersection(*(set(names) for names in routes)) if routes else set()
            inherited[file] = {name: set().union(*(names[name] for names in routes)) for name in common}
            active.discard(file)
        return merged(inherited[file], local(file, offset, {file}))

    return scope


def passes_name(tokens, name):
    """Return whether the tokens inside a macro invocation's delimiters hold the identifier that the name pattern
    matches where the macro may declare a module by it: outside attributes, the bodies of the functions they hold,
    paths, field accesses and the `mod name;` and `mod name {` items that the record reads in macro bodies."""
    skipped = [(function.body, function.end) for function in rust_functions(tokens)[0]]
    skipped += [(attribute.start(), after_closing(tokens, attribute.end() - 1)) for attribute in ATTRIBUTE.finditer(tokens)]
    for use in re.finditer(name, tokens):
        before, after = tokens[:use.start()].rstrip(), tokens[use.end():].lstrip()
        if not (any(start <= use.start() < end for start, end in skipped) or before.endswith(("::", ".")) or after.startswith("::")
                or re.search(r"\bmod$", before) and after.startswith((";", "{"))):
            return True
    return False


def hidden_declaration(file, parsed, path, builders, macros, scope, package):
    """Return the offset and kind of what may load path in file where the record cannot read the cfg around it.

    That is a `mod name;` inside a macro or function body, with the inline modules around it in a macro body, a
    `path = "..."` attribute setting there that names path's file name, an `include!("...")` there of a file that
    is path or names path's module or file name, or whose `env!("CARGO_MANIFEST_DIR")` path has no package to
    stand for, a macro invocation outside function bodies that holds a string
    naming path's file name, and an invocation of one of the builders macros that names path's module. So is an
    invocation outside function bodies of a macro that is not one of the readable macros, or that a path outside the
    crate names, when it may pass path's module on as the name of a module it declares. The invocations at item
    positions in a `macro_rules!` transcriber or a readable macro's invocation count too.
    """
    module = path.parent.name if path.name == "mod.rs" else path.stem
    names = re.compile(rf"\b{re.escape(module)}\b|{re.escape(path.name)}")
    mask, text = parsed.source.without_comments_or_strings, parsed.source.uncommented
    literals = dict(parsed.source.literals)
    bodies = [(function.body, function.end) for function in parsed.functions]
    for start, end in parsed.opaque + bodies:
        for match in HIDDEN_DECLARATION.finditer(mask, start, end):
            declaration = RustFunction(match[1], match.start(), match.start(), match.end() - 1, match.end())
            inner = []
            if (start, end) in parsed.opaque:
                for opening in HIDDEN_MODULE.finditer(mask, start, match.start()):
                    if match.start() < (close := after_closing(mask, opening.end() - 1)):
                        boundary = max([start] + [mask.rfind(c, start, opening.start()) for c in ";{}"]) + 1
                        inner.append(RustFunction(opening[1], boundary, opening.start(), opening.end() - 1, close))
            if match[1] == module and any(target.is_file() and target.resolve() == path for owner in (True, False)
                                          for target, _ in module_files(file, owner, parsed, declaration, inner)):
                return match.start(), HIDDEN
        for setting in HIDDEN_PATH.finditer(mask, start, end):
            value = string_value(text[setting.end():literals.get(setting.end(), setting.end())])
            if value is not None and Path(value).name == path.name:
                return setting.start(), HIDDEN
        for call in INCLUDE_CALL.finditer(mask, start, end):
            close = after_closing(mask, call.end() - 1)
            try:
                included = include_path(text[call.end():close - 1], file, package)
            except ValueError:
                return call.start(), INCLUDED
            if included is not None and included.is_file() and (
                    included.resolve() == path or names.search(included.read_text(encoding="utf-8", errors="replace"))):
                return call.start(), INCLUDED
    starts = [begin for begin, _ in parsed.source.literals]
    identifier = rf"\b{re.escape(module)}\b"
    named = rf"(?<![$@]){identifier}"
    for start, end in parsed.opaque:
        invoked = INVOKED.search(mask, max(0, start - 100), start)
        if invoked and invoked["name"] in INCLUDES or not (invoked or DEFINED.search(mask, max(0, start - 100), start)):
            continue
        if invoked and invoked["name"] in builders and re.search(identifier, mask[start:end]):
            return start, BUILT
        if any(body <= start < body_end for body, body_end in bodies):
            continue
        if re.search(identifier, mask[start:end]):
            visible = scope(file, start) if invoked else macros.every
            if invoked and not readable(invoked, macros, visible):
                if passes_name(mask[start + 1:end - 1], identifier):
                    return start, UNREAD
            else:
                regions = [(start + 1, end - 1)] if invoked else [(begin, stop) for _, begin, stop in transcribers(mask, start + 1, end - 1)]
                for nested, tokens in (found for begin, stop in regions for found in item_invocations(mask, begin, stop, macros, visible)):
                    if nested["name"] in builders and re.search(named, tokens):
                        return nested.start(), BUILT
                    if nested["name"] not in INCLUDES and not readable(nested, macros, visible) and passes_name(tokens, named):
                        return nested.start(), UNREAD
        if not invoked:
            continue
        for begin, stop in parsed.source.literals[bisect.bisect_left(starts, start):bisect.bisect_left(starts, end)]:
            if Path(string_value(text[begin:stop]) or "").name == path.name:
                return start, BUILT
    return None


def declaration_guards(path):
    """Return the guards on the out-of-line `mod` declarations that lead to path from its crate roots, outermost
    first. A crate root is one route without guards, since its own crate always compiles it, unless it is a lib.rs
    or main.rs that Cargo does not name and another file declares, which makes it a module. For more than one
    route, return `routes(...)` with each route as its crate root's path relative to path's directory, a colon and
    its guards, or `unguarded` for a route without any, sorted and separated by `; `.

    It follows each declaration from the crate roots by rustc's rules, including `#[path = "..."]` and each path
    that a cfg_attr may set, and each `include!("...")` item. It fails for a file that no root reaches, for a module
    declaration inside a macro or a function body of a reached file that may load path, and for a macro invocation
    there that may build one, such as an invocation of a macro from another crate that names path's module.
    """
    if (crates := crate_roots(path)) is None:
        return ""
    roots, named = crates
    edges, broken, packages = module_tree(roots)
    if path in roots and path not in edges:
        return ""
    module = path.parent.name if path.name == "mod.rs" else path.stem
    for message, text in broken:
        if text is None or re.search(rf"\b{re.escape(module)}\b|{re.escape(path.name)}", text):
            raise ValueError(message)
    parsed_files = []
    for file in sorted(set(roots) | edges.keys()):
        try:
            parsed_files.append((file, parse_rust(file)))
        except ValueError:
            continue
    builders = set().union(*(module_builders(parsed) for _, parsed in parsed_files))
    scope = textual_scopes(roots, edges)
    macros = readable_macros(parsed_files, builders)
    for file, parsed in parsed_files:
        if hidden := hidden_declaration(file, parsed, path, builders, macros, scope, packages.get(file)):
            offset, kind = hidden
            line = parsed.source.without_comments_or_strings.count("\n", 0, offset) + 1
            remedy = "if the macro declares no module, keep the module's name out of the invocation or rename the module" if kind == UNREAD else "declare the module outside macros and function bodies"
            raise ValueError(f"{file}:{line}: {kind} {path}, and the record cannot read the cfg around it; {remedy}")
    if path not in edges:
        unread = "".join(f"; {message}" for message, _ in broken)
        raise ValueError(f"{path}: no module declaration that the record can read leads to this file from a crate root; declare it with `mod <name>;` or `#[path = \"...\"]` outside macros and function bodies, in a file that a crate root reaches{unread}")

    def routes(file, visiting):
        root = file in named or file in roots and all(declarer == file for declarer, _ in edges.get(file, ()))
        found = [(file, "")] if root else []
        for declarer, declaration in edges.get(file, ()):
            if declarer in visiting:
                continue
            parsed = parse_rust(declarer)
            items = [(0, 0, -1)] + [(module.start, module.keyword, module.body) for module in enclosing_modules(parsed, declaration)] + [(declaration.start, declaration.keyword, declaration.body)]
            guards = cfg_guards(parsed.source, items)
            found += [(start, " ".join(filter(None, (route, guards)))) for start, route in routes(declarer, visiting | {declarer})]
        return found

    found = sorted((os.path.relpath(root, path.parent), guards) for root, guards in routes(path, {path}))
    if len(found) == 1:
        return found[0][1]
    labelled = "; ".join(f"{root}: {guards or 'unguarded'}" for root, guards in found)
    return f"routes({labelled})"


def kani_surface(path):
    source = rust_masks(path.read_text(encoding="utf-8"))
    text, mask = source.uncommented, source.without_comments_or_strings
    if renaming := RENAMING_IMPORT.search(mask):
        raise ValueError(f"{path}: '{collapse(renaming[0])}' brings a Kani assumption, cover, stub or harness attribute in under another name; write each as kani::<name> so the record can read it")
    functions, modules, opaque, _, _ = rust_functions(mask)
    declared = declaration_guards(path)

    def owner_at(position, *, attribute=False):
        if not any(start <= position < end for start, end in opaque):
            for function in reversed(functions):
                if function.start <= position < function.end and (position < function.body if attribute else position > function.body):
                    return function
        line = mask.count("\n", 0, position) + 1
        raise ValueError(f"{path}:{line}: cannot identify a function owner; write Kani forms in free functions under inline modules, outside macro definitions and impl or trait bodies")

    surface = Surface()
    spans, read = [], []
    for kind, pattern in MACROS:
        for match in pattern.finditer(mask):
            end = after_closing(mask, match.end() - 1)
            read.append((match.start(), end))
            argument = rust_masks(text[match.end():end - 1])
            owner = owner_at(match.start(), attribute=kind == "stub").name
            spans.append((match.start(), f"{kind} {collapse(argument.uncommented, argument.literals)} in {owner}", ""))
    for match in PROOF.finditer(mask):
        read.append(match.span())
        harness = owner_at(match.start(), attribute=True)
        enclosing = sorted((item for item in functions + modules if item.start <= harness.start and harness.end <= item.end), key=lambda item: item.start)
        guards = " ".join(filter(None, (declared, cfg_guards(source, [(0, 0, -1)] + [(item.start, item.keyword, item.body) for item in enclosing]))))
        spans.append((match.start(), f"harness {harness.name}", guards))
    for token in KANI_TOKEN.finditer(mask):
        if not any(start <= token.start() < end for start, end in read):
            line = mask.count("\n", 0, token.start()) + 1
            raise ValueError(f"{path}:{line}: '{collapse(token[0])}' is in a form the record cannot read; write kani::assume(...), kani::any_where(...), kani::cover!(...), #[kani::stub(...)] or #[kani::proof], alone or under #[cfg_attr(kani, ...)]")
    for _, item, guards in sorted(spans):
        surface.add(item, guards)
    return surface


SURFACES = {"lean": lean_surface, "tla": tla_surface, "kani": kani_surface}


def digest(surface):
    return hashlib.sha256(json.dumps(surface, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")).hexdigest()


def read_record(path):
    record = json.loads(path.read_text(encoding="utf-8"))
    models = record.get("models") if isinstance(record, dict) else None
    if not isinstance(models, dict) or record.get("format") != FORMAT:
        raise ValueError(f"{path}: unsupported record format; run record with a new record file")
    for model, entry in models.items():
        if not isinstance(entry, dict) or entry.get("kind") not in SURFACES or not isinstance(entry.get("surface"), dict):
            raise ValueError(f"{path}: malformed entry for {model}")
    return models


def write_record(path, models):
    path.parent.mkdir(parents=True, exist_ok=True)
    runner.atomic_write(path, json.dumps({"format": FORMAT, "models": models}, ensure_ascii=False, indent=2, sort_keys=True) + "\n")


def record(record_path, files):
    for file in files:
        if file.suffix not in KINDS:
            print(f"usage: {file} has no model surface; expected one of {', '.join(KINDS)}")
            return 2
    models = read_record(record_path) if record_path.exists() else {}
    updates = {}
    for file in files:
        kind = KINDS[file.suffix]
        surface = SURFACES[kind](file.resolve())
        updates[str(file.resolve())] = {"kind": kind, "digest": digest(surface), "surface": surface}
    for model, entry in updates.items():
        print(f"RECORDED {model} {entry['digest']}")
        previous = models.get(model, {}).get("digest")
        if previous and previous != entry["digest"]:
            print(f"  previous {previous}")
    write_record(record_path, {**models, **updates})
    return 0


KANI_KEY = re.compile(r"(harness |(?:assume|cover|stub) .* in )(\S+)( #\d+)?", re.DOTALL)


def renamed(surface, old_module, new_module):
    """Rewrite each Kani owner under old_module to sit under new_module, where `crate` is the file's root."""
    old, new = ([] if path == "crate" else path.split("::") for path in (old_module, new_module))
    result = {}
    for name, value in surface.items():
        head, owner, duplicate = KANI_KEY.fullmatch(name).groups()
        parts = owner.split("::")
        if parts[:len(old)] == old:
            owner = "::".join(new + parts[len(old):])
        result[f"{head}{owner}{duplicate or ''}"] = value
    if len(result) != len(surface):
        raise ValueError(f"renaming {old_module} to {new_module} merges recorded items")
    return result


def move(record_path, old_file, new_file, module):
    models = read_record(record_path) if record_path.is_file() else {}
    old, new = str(old_file.resolve()), str(new_file.resolve())
    if old not in models:
        print(f"usage: {old} has no record entry; record it before the move")
        return 2
    kind = models[old]["kind"]
    if KINDS.get(new_file.suffix) != kind:
        print(f"usage: {new} is not a {kind} model file")
        return 2
    if module and kind != "kani":
        print("usage: --module applies only to a Kani harness file")
        return 2
    surface = models.pop(old)["surface"]
    if module:
        surface = renamed(surface, *module)
    if new in models:
        if overlap := surface.keys() & models[new]["surface"].keys():
            raise ValueError(f"{new} already records {', '.join(sorted(overlap))}")
        surface = {**models[new]["surface"], **surface}
    models[new] = {"kind": kind, "digest": digest(surface), "surface": surface}
    write_record(record_path, models)
    print(f"MOVED {old} -> {new}")
    return 0


def differences(kind, old, new):
    lines = []
    if kind == "tla" and not any(name.startswith("imports ") for name in old):
        lines.append("  previous baseline did not track imported modules; review and record this matrix again")
    if kind == "tla" and "TLA+ layout version" not in old:
        lines.append("  previous baseline did not preserve TLA+ layout; review and record this matrix again")
    for name in old:
        if name not in new:
            lines.append(f"  removed {name}")
        elif old[name] != new[name]:
            lines += [f"  changed {name}", f"    old: {old[name]}", f"    new: {new[name]}"]
    lines += [f"  added {name}" for name in new if name not in old and name.split(" ", 1)[0] in NARROWING[kind]]
    return lines


def compare(record_path):
    if not record_path.is_file():
        print(f"usage: record file {record_path} does not exist; run record first")
        return 2
    models = read_record(record_path)
    changed = 0
    for model, entry in models.items():
        try:
            if not Path(model).is_file():
                lines = ["  file is missing"]
            else:
                lines = differences(entry["kind"], entry["surface"], SURFACES[entry["kind"]](Path(model)))
        except (OSError, ValueError, KeyError, TypeError) as error:
            lines = [f"  FAIL {error}"]
        changed += bool(lines)
        print(f"{'CHANGED' if lines else 'UNCHANGED'} {model}")
        if lines:
            print("\n".join(lines))
    print(f"SUMMARY {len(models) - changed} unchanged, {changed} changed")
    return int(changed > 0)


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    commands = parser.add_subparsers(dest="command", required=True)
    recording = commands.add_parser("record", help="record or update the entries for these model files")
    recording.add_argument("record_file", type=Path)
    recording.add_argument("models", nargs="+", type=Path)
    commands.add_parser("compare", help="compare every recorded model with its file").add_argument("record_file", type=Path)
    moving = commands.add_parser("move", help="move a model's recorded entry to the file it moved to")
    moving.add_argument("record_file", type=Path)
    moving.add_argument("old_file", type=Path)
    moving.add_argument("new_file", type=Path)
    moving.add_argument("--module", nargs=2, metavar=("OLD", "NEW"),
                        help="the Kani harnesses moved from module OLD to NEW; crate names the file's root")
    arguments = parser.parse_args()
    if arguments.command == "record":
        return record(arguments.record_file, arguments.models)
    if arguments.command == "move":
        return move(arguments.record_file, arguments.old_file, arguments.new_file, arguments.module)
    return compare(arguments.record_file)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f"FAIL baseline: {error}")
        sys.exit(1)
