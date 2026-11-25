// Copyright (c) 2026 Michael Denyer
// SPDX-License-Identifier: GPL-3.0-only
import assert from "node:assert/strict";
import { copyFileSync, mkdirSync, readFileSync, realpathSync, rmSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { afterEach, test } from "node:test";
import { fixture, removeFixtures, root, run } from "./helpers.mjs";

afterEach(removeFixtures);

const examples = join(root, "skills/formal-verify/examples");

function models() {
  const dir = realpathSync(fixture());
  for (const folder of ["tla", "lean", "kani"]) mkdirSync(join(dir, folder));
  const paths = {
    matrix: join(dir, "tla/BoundedQueue.matrix"),
    spec: join(dir, "tla/BoundedQueue.tla"),
    statements: join(dir, "lean/BoundedQueue.statements"),
    rust: join(dir, "kani/lib.rs"),
    record: join(dir, "record.json"),
  };
  // The TLA+ cases edit this counter spec's exact text, so they read a fixed copy rather than the template.
  copyFileSync(join(root, "tests/fixtures/tla-baseline/BoundedQueue.matrix"), paths.matrix);
  copyFileSync(join(root, "tests/fixtures/tla-baseline/BoundedQueue.tla"), paths.spec);
  copyFileSync(join(examples, "lean-template/Model/BoundedQueue.statements"), paths.statements);
  copyFileSync(join(examples, "kani-template/src/lib.rs"), paths.rust);
  return { dir, ...paths };
}

const baseline = (dir, ...args) => run(dir, "baseline.py", args);
const lines = (result) => result.stdout.split("\n").filter(Boolean);

function edit(path, from, to) {
  const text = readFileSync(path, "utf8");
  assert.ok(text.includes(from), `${path} lacks ${JSON.stringify(from)}`);
  writeFileSync(path, text.replace(from, to));
}

function rewriteStatements(path, change) {
  const record = JSON.parse(readFileSync(path, "utf8"));
  change(record);
  writeFileSync(path, JSON.stringify(record, null, 2) + "\n");
}

function recordedThenEdited(setup, target, change) {
  const files = models();
  setup?.(files);
  assert.equal(baseline(files.dir, "record", files.record, files[target]).status, 0);
  change(files);
  const result = baseline(files.dir, "compare", files.record);
  return { files, result, out: lines(result) };
}

function assertChanged({ files, result, out }, target, ...details) {
  assert.equal(result.status, 1);
  assert.equal(out[0], `CHANGED ${files[target]}`);
  assert.equal(out.at(-1), "SUMMARY 0 unchanged, 1 changed");
  for (const detail of details) assert.ok(out.some((line) => line.includes(detail)), `${JSON.stringify(out)} lacks ${detail}`);
}

function assertUnchanged({ files, result, out }, target) {
  assert.equal(result.status, 0);
  assert.deepEqual(out, [`UNCHANGED ${files[target]}`, "SUMMARY 1 unchanged, 0 changed"]);
}

const tla = (from, to) => (change) => edit(change.spec, from, to);
const rust = (from, to) => (change) => edit(change.rust, from, to);

test("a re-frozen Lean declaration is changed and named, whichever hash moved", () => {
  for (const field of ["typeHash", "valueHash"]) {
    const outcome = recordedThenEdited(null, "statements", ({ statements }) =>
      rewriteStatements(statements, (record) => {
        record.declarations.find((entry) => entry.name === "BoundedQueue.Invariant")[field] = "0".repeat(64);
      }));
    assertChanged(outcome, "statements", "changed declaration BoundedQueue.Invariant");
  }
});

test("a Lean declaration added after the record is allowed", () => {
  const outcome = recordedThenEdited(null, "statements", ({ statements }) =>
    rewriteStatements(statements, (record) => {
      record.declarations.push({ name: "BoundedQueue.helper", kind: "theorem", type: "True", typeHash: "1".repeat(64), valueHash: null });
    }));
  assertUnchanged(outcome, "statements");
});

test("a removed Lean declaration and a changed toolchain are changed", () => {
  const removed = recordedThenEdited(null, "statements", ({ statements }) =>
    rewriteStatements(statements, (record) => {
      record.declarations = record.declarations.filter((entry) => entry.name !== "BoundedQueue.claim");
    }));
  assertChanged(removed, "statements", "removed declaration BoundedQueue.claim");
  const toolchain = recordedThenEdited(null, "statements", ({ statements }) =>
    rewriteStatements(statements, (record) => {
      record.toolchain = "leanprover/lean4:v4.0.0";
    }));
  assertChanged(toolchain, "statements", "changed toolchain");
});

test("a TLA+ check line that loses a property is changed", () => {
  const outcome = recordedThenEdited(null, "matrix", ({ matrix }) => edit(matrix, "check INVARIANTS TypeOK InWindow", "check INVARIANTS TypeOK"));
  assertChanged(outcome, "matrix", "removed check BoundedQueue.tla INVARIANTS InWindow");
});

test("moving TLA+ checks below their runs loses those runs' guarantees", () => {
  const outcome = recordedThenEdited(null, "matrix", ({ matrix }) => {
    const text = readFileSync(matrix, "utf8");
    const checks = text.split("\n").filter((line) => line.startsWith("check "));
    writeFileSync(matrix, text.split("\n").filter((line) => !line.startsWith("check ")).join("\n") + checks.join("\n") + "\n");
  });
  assertChanged(outcome, "matrix", "removed check BoundedQueue.tla INVARIANTS InWindow");
});

test("a TLA+ reach check records the first matching run's inputs", () => {
  const setup = ({ matrix }) => edit(matrix, "reach WindowFull | window=1", "reach WindowFull | window=");
  const outcome = recordedThenEdited(setup, "matrix", ({ matrix }) => {
    const text = readFileSync(matrix, "utf8");
    const runs = text.split("\n").filter((line) => line.startsWith("run "));
    writeFileSync(matrix, text.split("\n").filter((line) => !line.startsWith("run ")).join("\n") + runs.reverse().join("\n") + "\n");
  });
  assertChanged(outcome, "matrix", "changed reach BoundedQueue.tla WindowFull");
});

test("repeated TLA+ spec sections keep their checks attached to their own runs", () => {
  const setup = ({ matrix }) => writeFileSync(matrix, [
    "spec BoundedQueue.tla", "check INVARIANTS TypeOK InWindow", "run first | Window=1 Items=3",
    "spec BoundedQueue.tla", "check INVARIANTS TypeOK", "run second | Window=2 Items=3", "",
  ].join("\n"));
  const outcome = recordedThenEdited(setup, "matrix", ({ matrix }) => {
    edit(matrix, "check INVARIANTS TypeOK InWindow", "check INVARIANTS TypeOK");
    edit(matrix, "run second", "check INVARIANTS InWindow\nrun second");
  });
  assertChanged(outcome, "matrix", "removed check BoundedQueue.tla INVARIANTS InWindow | [run BoundedQueue.tla first]");
});

test("adding a TLA+ check strengthens an existing run without changing its baseline", () => {
  const setup = ({ matrix }) => edit(matrix, "check INVARIANTS TypeOK InWindow", "check INVARIANTS TypeOK");
  const outcome = recordedThenEdited(setup, "matrix", ({ matrix }) => edit(matrix, "check INVARIANTS TypeOK", "check INVARIANTS TypeOK InWindow"));
  assertUnchanged(outcome, "matrix");
});

test("duplicate TLA+ checks cannot stand in for a check on a different occurrence of the same run label", () => {
  const section = "spec BoundedQueue.tla\ncheck INVARIANTS TypeOK InWindow\nrun same | Window=1 Items=3\n";
  const setup = ({ matrix }) => writeFileSync(matrix, section + section);
  const outcome = recordedThenEdited(setup, "matrix", ({ matrix }) => writeFileSync(matrix,
    section.replace("TypeOK InWindow", "TypeOK InWindow InWindow") + section.replace("TypeOK InWindow", "TypeOK")));
  assertChanged(outcome, "matrix", "removed check BoundedQueue.tla INVARIANTS InWindow");
});

test("an unedited matrix that repeats a spec section compares unchanged", () => {
  const section = "spec BoundedQueue.tla\ncheck INVARIANTS TypeOK InWindow\nrun same | Window=1 Items=3\n";
  const setup = ({ matrix }) => writeFileSync(matrix, section + section);
  assertUnchanged(recordedThenEdited(setup, "matrix", () => {}), "matrix");
});

test("a TLA+ Spec that loses fairness is changed", () => {
  assertChanged(recordedThenEdited(null, "matrix", tla(" /\\ WF_vars(Consume)", "")), "matrix", "changed definition BoundedQueue.tla Spec");
});

test("a TLA+ subscript that Spec names under [][...]_ and WF_ is changed", () => {
  const outcome = recordedThenEdited(null, "matrix", tla("vars == <<next, consumed>>", "vars == <<next>>"));
  assertChanged(outcome, "matrix", "changed definition BoundedQueue.tla vars");
});

test("a TLA+ subscript is followed in a fairness definition, under a quantifier and after spaces", () => {
  const spec = "Spec == Init /\\ [][Next]_vars /\\ WF_vars(Claim) /\\ WF_vars(Consume)";
  const shapes = [
    "Fairness == WF_vars(Claim) /\\ WF_vars(Consume)\nSpec == Init /\\ [][Next]_<<next, consumed>> /\\ Fairness",
    "Act(k) == Claim \\/ Consume\nSpec == Init /\\ [][Next]_<<next, consumed>> /\\ \\A k \\in {1} : WF_vars(Act(k))",
    "Spec == Init /\\ [] [Next]_vars",
    "Spec == Init /\\ [][Next]_<<next, consumed>> /\\ []<><<Consume>>_vars",
  ];
  for (const shape of shapes) {
    const setup = (files) => {
      edit(files.spec, "UNCHANGED vars", "UNCHANGED <<next, consumed>>");
      edit(files.spec, spec, shape);
    };
    const outcome = recordedThenEdited(setup, "matrix", tla("vars == <<next, consumed>>", "vars == <<next>>"));
    assertChanged(outcome, "matrix", "changed definition BoundedQueue.tla vars");
  }
});

test("a weakened TLA+ property is changed", () => {
  const outcome = recordedThenEdited(null, "matrix", tla("next <= consumed + Window", "next <= consumed + Window + 1"));
  assertChanged(outcome, "matrix", "changed definition BoundedQueue.tla InWindow");
});

test("a TLA+ helper that a property references is changed, and an action that none references is not", () => {
  const helper = tla("AllConsumed == <>(consumed = Items)", "Finished == consumed = Items\nAllConsumed == <>Finished");
  const outcome = recordedThenEdited(helper, "matrix", tla("Finished == consumed = Items", "Finished == consumed >= 0"));
  assertChanged(outcome, "matrix", "changed definition BoundedQueue.tla Finished");
  assertUnchanged(recordedThenEdited(null, "matrix", tla("next' = next + 1", "next' = next + 2")), "matrix");
});

test("a TLA+ operator that only a function definition's domain references is changed", () => {
  const helper = tla("InWindow == consumed <= next /\\ next <= consumed + Window",
    "Slots == 0..Window\nFits[k \\in Slots] == next <= consumed + k\nInWindow == consumed <= next /\\ \\E k \\in DOMAIN Fits : Fits[k]");
  const outcome = recordedThenEdited(helper, "matrix", tla("Slots == 0..Window", "Slots == 0..Items"));
  assertChanged(outcome, "matrix", "changed definition BoundedQueue.tla Slots");
});

test("TLA+ properties follow transitive local imports and leave unrelated action bodies free to change", () => {
  function setup(files) {
    edit(files.spec, "EXTENDS Naturals", "EXTENDS Naturals,\n  Predicates");
    edit(files.spec, "AllConsumed == <>(consumed = Items)", "AllConsumed == <>Finished(consumed, Items)");
    writeFileSync(join(files.dir, "tla/Predicates.tla"),
      "---- MODULE Predicates ----\nEXTENDS Limits\nFinished(n, total) == Equal(n, total)\n====\n");
    writeFileSync(join(files.dir, "tla/Limits.tla"),
      "---- MODULE Limits ----\nEqual(n, m) == n = m\nOtherAction == TRUE\n====\n");
  }
  const change = (from, to) => ({ dir }) => edit(join(dir, "tla/Limits.tla"), from, to);
  assertChanged(recordedThenEdited(setup, "matrix", change("n = m", "TRUE")), "matrix", "changed definition Limits.tla Equal");
  assertUnchanged(recordedThenEdited(setup, "matrix", change("OtherAction == TRUE", "OtherAction == FALSE")), "matrix");
});

test("a multi-line LOCAL definition with a tab after LOCAL does not hide the imported operator of that name", () => {
  function setup(files) {
    edit(files.spec, "EXTENDS Naturals", "EXTENDS Naturals, Shared, Hidden");
    edit(files.spec, "AllConsumed == <>(consumed = Items)", "AllConsumed == <>Finished(consumed, Items)");
    writeFileSync(join(files.dir, "tla/Shared.tla"), "---- MODULE Shared ----\nFinished(n, total) == n = total\n====\n");
    writeFileSync(join(files.dir, "tla/Hidden.tla"), "---- MODULE Hidden ----\nLOCAL\tFinished(n, total) ==\n  TRUE\n====\n");
  }
  assertChanged(recordedThenEdited(setup, "matrix", ({ dir }) => edit(join(dir, "tla/Shared.tla"), "n = total", "TRUE")),
    "matrix", "changed definition Shared.tla Finished");
});

test("a locally imported operator with an indented header is tracked", () => {
  const setup = (files) => {
    edit(files.spec, "EXTENDS Naturals", "EXTENDS Naturals, Limits");
    edit(files.spec, "AllConsumed == <>(consumed = Items)", "AllConsumed == <>Equal(consumed, Items)");
    writeFileSync(join(files.dir, "tla/Limits.tla"), "---- MODULE Limits ----\n  Equal(n, m) == n = m\n====\n");
  };
  assertChanged(recordedThenEdited(setup, "matrix", ({ dir }) =>
    edit(join(dir, "tla/Limits.tla"), "n = m", "TRUE")), "matrix", "Limits.tla");
});

test("a local TLA+ instance retains both its operator bodies and its substitutions", () => {
  function setup(files) {
    edit(files.spec, "AllConsumed == <>(consumed = Items)",
      "Bounds == INSTANCE Limit WITH Max <- Items\nAllConsumed == <>Bounds!Finished(consumed)");
    writeFileSync(join(files.dir, "tla/Limit.tla"),
      "---- MODULE Limit ----\nCONSTANT Max\nFinished(n) == n = Max\n====\n");
  }
  assertChanged(recordedThenEdited(setup, "matrix", ({ dir }) =>
    edit(join(dir, "tla/Limit.tla"), "n = Max", "TRUE")), "matrix", "Limit.tla");
  assertChanged(recordedThenEdited(setup, "matrix", tla("Max <- Items", "Max <- Window")), "matrix", "BoundedQueue.tla");
});

test("pre-import TLA+ baselines require review and can be recorded again", () => {
  const files = models();
  assert.equal(baseline(files.dir, "record", files.record, files.matrix).status, 0);
  const record = JSON.parse(readFileSync(files.record, "utf8"));
  delete record.models[files.matrix].surface["imports BoundedQueue.tla"];
  writeFileSync(files.record, JSON.stringify(record));
  const compared = baseline(files.dir, "compare", files.record);
  assert.equal(compared.status, 1);
  assert.match(compared.stdout, /previous baseline did not track imported modules/);
  assert.equal(baseline(files.dir, "record", files.record, files.matrix).status, 0);
  assert.equal(baseline(files.dir, "compare", files.record).status, 0);
});

test("a pre-layout TLA+ record requires review even if the model has only single-line definitions", () => {
  const files = models();
  assert.equal(baseline(files.dir, "record", files.record, files.matrix).status, 0);
  const record = JSON.parse(readFileSync(files.record, "utf8"));
  delete record.models[files.matrix].surface["TLA+ layout version"];
  writeFileSync(files.record, JSON.stringify(record));
  const result = baseline(files.dir, "compare", files.record);
  assert.equal(result.status, 1);
  assert.match(result.stdout, /did not preserve TLA\+ layout/);
});

test("indented LET definitions keep per-definition records for actions and properties", () => {
  const setup = (files) => {
    edit(files.spec, "         /\\ next' = next + 1", "         /\\ LET step == 1\n            IN next' = next + step");
    edit(files.spec, "AllConsumed == <>(consumed = Items)", "AllConsumed ==\n    LET done == consumed = Items\n    IN <>done");
  };
  assertUnchanged(recordedThenEdited(setup, "matrix", tla("step == 1", "step == 2")), "matrix");
  assertChanged(recordedThenEdited(setup, "matrix", tla("done == consumed = Items", "done == consumed >= 0")),
    "matrix", "changed definition BoundedQueue.tla AllConsumed");
});

test("a nested LET closes only its own scope, so a later definition of the outer LET stays local", () => {
  const setup = tla("AllConsumed == <>(consumed = Items)",
    "AllConsumed ==\n    LET done == LET all == Items IN consumed = all\n        also == TRUE\n    IN <>(done /\\ also)");
  assertChanged(recordedThenEdited(setup, "matrix", tla("also == TRUE", "also == FALSE")),
    "matrix", "changed definition BoundedQueue.tla AllConsumed");
});

test("an imported module with an indented LET definition keeps per-definition records", () => {
  const setup = (files) => {
    edit(files.spec, "EXTENDS Naturals", "EXTENDS Naturals, Limits");
    edit(files.spec, "AllConsumed == <>(consumed = Items)", "AllConsumed == <>Equal(consumed, Items)");
    writeFileSync(join(files.dir, "tla/Limits.tla"),
      "---- MODULE Limits ----\nEqual(n, m) ==\n  LET same == n = m IN same\nOtherAction == TRUE\n====\n");
  };
  const change = (from, to) => ({ dir }) => edit(join(dir, "tla/Limits.tla"), from, to);
  assertChanged(recordedThenEdited(setup, "matrix", change("same == n = m", "same == TRUE")), "matrix", "changed definition Limits.tla Equal");
  assertUnchanged(recordedThenEdited(setup, "matrix", change("OtherAction == TRUE", "OtherAction == FALSE")), "matrix");
});

test("an indented TLA+ definition after a LET closes, or a column-0 one inside a LET, compares the whole module", () => {
  for (const replacement of [
    "Unused ==\n  LET one == 1 IN one\n  Finished == consumed = Items\nAllConsumed == <>Finished",
    "AllConsumed ==\n  LET\nFinished == consumed = Items\n  IN <>Finished",
    "AllConsumed ==\n  LET Finished == consumed = Items\na ++ b == a + b\n  IN <>Finished",
  ]) {
    const setup = tla("AllConsumed == <>(consumed = Items)", replacement);
    assertChanged(recordedThenEdited(setup, "matrix", tla("Finished == consumed = Items", "Finished == TRUE")),
      "matrix", "changed module text");
  }
});

test("a TLA+ Init that Spec narrows is changed", () => {
  assertChanged(recordedThenEdited(null, "matrix", tla("Init == next = 0 /\\ consumed = 0", "Init == next = 0 /\\ consumed = 0 /\\ Items = 0")), "matrix", "changed definition BoundedQueue.tla Init");
});

test("an edit on an unindented continuation line of a TLA+ property is changed", () => {
  const unindented = tla("InWindow == consumed <= next /\\ next <= consumed + Window", "InWindow ==\nconsumed <= next /\\\nnext <= consumed + Window");
  const outcome = recordedThenEdited(unindented, "matrix", tla("\nnext <= consumed + Window", "\nnext <= consumed + Window + 1"));
  assertChanged(outcome, "matrix", "changed definition BoundedQueue.tla InWindow");
});

test("a TLA+ operator with an operator parameter is its own recorded definition", () => {
  const higherOrder = (files) => {
    edit(files.spec, "InWindow == consumed <= next /\\ next <= consumed + Window", "InWindow == consumed <= next /\\ next <= consumed + Window /\\ Holds(Bounded)");
    edit(files.spec, "\nSpec ==", "\nBounded(n) == n >= 0\nHolds(P(_)) == P(next)\n\nSpec ==");
  };
  const outcome = recordedThenEdited(higherOrder, "matrix", tla("Holds(P(_)) == P(next)", "Holds(P(_)) == TRUE"));
  assertChanged(outcome, "matrix", "changed definition BoundedQueue.tla Holds");
});

test("TLA+ definitions with nested brackets or a leading digit are their own recorded definitions", () => {
  const named = (files) => {
    edit(files.spec, "InWindow == consumed <= next /\\ next <= consumed + Window", "InWindow == consumed <= next /\\ next <= 1aBound /\\ Pair[[a |-> 0]] = 0");
    edit(files.spec, "\nSpec ==", "\n1aBound == consumed + Window\nPair[r \\in [a : {0, 1}]] == r.a\n\nSpec ==");
  };
  assertChanged(recordedThenEdited(named, "matrix", tla("1aBound == consumed + Window", "1aBound == consumed + Window + 1")), "matrix", "changed definition BoundedQueue.tla 1aBound");
  assertChanged(recordedThenEdited(named, "matrix", tla("== r.a", "== 0")), "matrix", "changed definition BoundedQueue.tla Pair");
});

test("a column-0 TLA+ definition the record cannot name is recorded whether or not a property names it", () => {
  const infix = (files) => edit(files.spec, "\nSpec ==", "\na \\prec b == a < b\n\nSpec ==");
  assertChanged(recordedThenEdited(infix, "matrix", tla("a \\prec b == a < b", "a \\prec b == a <= b")), "matrix", "changed definition BoundedQueue.tla a \\prec b");
  const local = tla("InWindow == consumed <= next /\\ next <= consumed + Window", "InWindow ==\nLET d == consumed + Window IN\nconsumed <= next /\\ next <= d");
  assertChanged(recordedThenEdited(local, "matrix", tla("consumed + Window IN", "consumed + Window + 1 IN")), "matrix", "changed definition BoundedQueue.tla LET d");
});

test("a TLA+ comment edit and an added run line leave the model unchanged", () => {
  assertUnchanged(recordedThenEdited(null, "matrix", tla("\\* Stutter at the end", "\\* Stutters at the very end")), "matrix");
  assertUnchanged(recordedThenEdited(null, "matrix", tla("consumed <= next /\\", "consumed <=   next (* why *) /\\")), "matrix");
  assertUnchanged(recordedThenEdited(null, "matrix", ({ matrix }) => edit(matrix, "run window=4 items=0 | Window=4 Items=0", "run window=4 items=0 | Window=4 Items=0\nrun window=2 items=2 | Window=2 Items=2")), "matrix");
});

test("TLA+ comment markers inside strings do not hide changes to a property", () => {
  for (const literal of [String.raw`"(*"`, String.raw`"\\*"`, String.raw`"\"(*"`]) {
    const property = `AllConsumed == <>(consumed = Items) /\\ ${literal} # "bad"`;
    const setup = tla("AllConsumed == <>(consumed = Items)", property);
    assertChanged(recordedThenEdited(setup, "matrix", tla(' # "bad"', ' # "worse"')), "matrix", "changed definition BoundedQueue.tla AllConsumed");
  }
});

test("whitespace inside TLA+ string literals is part of the property", () => {
  const setup = tla("AllConsumed == <>(consumed = Items)", 'AllConsumed == <>(consumed = Items) /\\ "a b" # "a  b"');
  assertChanged(recordedThenEdited(setup, "matrix", tla('"a  b"', '"a b"')), "matrix", "changed definition BoundedQueue.tla AllConsumed");
});

test("a TLA+ run whose constants change is changed", () => {
  const outcome = recordedThenEdited(null, "matrix", ({ matrix }) => edit(matrix, "Window=4 Items=5", "Window=4 Items=1"));
  assertChanged(outcome, "matrix", "changed run BoundedQueue.tla window=4 items=5");
});

test("a TLA+ property that names a missing operator fails", () => {
  const files = models();
  edit(files.matrix, "check PROPERTIES AllConsumed", "check PROPERTIES NoSuchProperty");
  const result = baseline(files.dir, "record", files.record, files.matrix);
  assert.equal(result.status, 1);
  assert.ok(lines(result)[0].startsWith("FAIL baseline:"));
  assert.ok(result.stdout.includes("NoSuchProperty"));
});

test("a malformed matrix line fails the record", () => {
  const files = models();
  edit(files.matrix, "reach WindowFull | window=1", "reach WindowFull");
  const result = baseline(files.dir, "record", files.record, files.matrix);
  assert.equal(result.status, 1);
  assert.ok(result.stdout.includes("malformed reach"));
});

test("an added Kani assume is changed", () => {
  const outcome = recordedThenEdited(null, "rust", rust("kani::assume(window > 0 && window <= 2);", "kani::assume(window > 0 && window <= 2);\n        kani::assume(state.next == 0);"));
  assertChanged(outcome, "rust", "added assume state.next == 0");
});

test("a cfg that can switch a recorded Kani harness off is changed, and cfg(kani) is not", () => {
  const guarded = recordedThenEdited(null, "rust", rust("    #[kani::proof]\n    #[kani::unwind(2)]\n    fn consume_keeps_invariant", "    #[cfg(feature = \"slow-proofs\")]\n    #[kani::proof]\n    #[kani::unwind(2)]\n    fn consume_keeps_invariant"));
  assertChanged(guarded, "rust", "changed harness proofs::consume_keeps_invariant", 'new: cfg(feature = "slow-proofs")');
  const module = recordedThenEdited(null, "rust", rust("#[cfg(kani)]\nmod proofs {", "#[cfg(kani)]\n#[cfg(not(miri))]\nmod proofs {\n    #![cfg(target_os = \"linux\")]"));
  assertChanged(module, "rust", "changed harness proofs::claim_keeps_invariant", 'new: cfg(not(miri)) cfg(target_os = "linux")');
  const file = recordedThenEdited(null, "rust", ({ rust: path }) => writeFileSync(path, `#![cfg(unix)]\n${readFileSync(path, "utf8")}`));
  assertChanged(file, "rust", "new: cfg(unix)");
  const setup = ({ rust: path }) => writeFileSync(path, "#[cfg(feature = \"a\")] #[kani::proof] fn first() {}");
  assertChanged(recordedThenEdited(setup, "rust", rust("#[cfg(feature = \"a\")] ", "")), "rust", 'old: cfg(feature = "a")');
  const nested = ({ rust: path }) => writeFileSync(path, "#[cfg(b)] mod m { #![cfg(c)] fn outer() { #[cfg(d)] #[kani::proof] fn inner() {} } }");
  const removed = recordedThenEdited(nested, "rust", rust("#[cfg(b)] ", ""));
  assertChanged(removed, "rust", "changed harness m::outer::inner");
  assert.ok(removed.out.includes("    old: cfg(b) cfg(c) cfg(d)"), JSON.stringify(removed.out));
  const attribute = recordedThenEdited(setup, "rust", rust("#[kani::proof]", "#[cfg_attr(kani, cfg(not(miri)))] #[kani::proof]"));
  assertChanged(attribute, "rust", 'new: cfg(feature = "a") cfg_attr(kani, cfg(not(miri)))');
  const marked = recordedThenEdited(setup, "rust", ({ rust: path }) => writeFileSync(path, `\ufeff#![cfg(unix)]\n${readFileSync(path, "utf8")}`));
  assertChanged(marked, "rust", 'new: cfg(unix) cfg(feature = "a")');
  const kani = recordedThenEdited(null, "rust", rust("    #[kani::proof]\n    #[kani::unwind(2)]\n    fn consume_keeps_invariant", "    #[cfg( kani )]\n    #[kani::proof]\n    #[kani::unwind(2)]\n    fn consume_keeps_invariant"));
  assertUnchanged(kani, "rust");
});

test("a cfg on the out-of-line mod declarations that lead to a recorded Kani harness file is changed", () => {
  const crate = (files) => {
    const dir = realpathSync(fixture());
    for (const [name, text] of Object.entries(files)) {
      mkdirSync(join(dir, name, ".."), { recursive: true });
      writeFileSync(join(dir, name), text);
    }
    return dir;
  };
  const harness = "#[kani::proof]\nfn a() { kani::cover!(true); }\n";
  const both = crate({ "lib.rs": "#[cfg(kani)]\nmod proofs;\n", "proofs.rs": harness });
  const [lib, proofs, record] = ["lib.rs", "proofs.rs", "record.json"].map((name) => join(both, name));
  assert.equal(baseline(both, "record", record, lib, proofs).status, 0);
  edit(lib, "mod proofs;", '#[cfg(feature = "slow-proofs")]\nmod proofs;');
  const added = baseline(both, "compare", record);
  assert.equal(added.status, 1);
  assert.deepEqual(lines(added), [`UNCHANGED ${lib}`, `CHANGED ${proofs}`, "  changed harness a", "    old: ", '    new: cfg(feature = "slow-proofs")', "SUMMARY 1 unchanged, 1 changed"]);

  const nested = crate({
    "src/lib.rs": "#![cfg(unix)]\n#[cfg(a)]\nmod verify;\n#[cfg(d)] pub mod checks;\n",
    "src/verify.rs": "mod inner {\n    #[cfg(b)]\n    mod proofs;\n}\n",
    "src/verify/inner/proofs.rs": harness,
    "src/checks/mod.rs": harness,
  });
  const [inner, checks, nestedRecord] = ["src/verify/inner/proofs.rs", "src/checks/mod.rs", "record.json"].map((name) => join(nested, name));
  assert.equal(baseline(nested, "record", nestedRecord, inner, checks).status, 0);
  edit(join(nested, "src/lib.rs"), "#[cfg(a)]\n", "");
  edit(join(nested, "src/lib.rs"), "#[cfg(d)] ", "");
  assert.deepEqual(lines(baseline(nested, "compare", nestedRecord)), [
    `CHANGED ${checks}`, "  changed harness a", "    old: cfg(unix) cfg(d)", "    new: cfg(unix)",
    `CHANGED ${inner}`, "  changed harness a", "    old: cfg(unix) cfg(a) cfg(b)", "    new: cfg(unix) cfg(b)",
    "SUMMARY 0 unchanged, 2 changed",
  ]);

  const guards = (files, target) => {
    const dir = crate(files);
    const recordPath = join(dir, "record.json");
    assert.equal(baseline(dir, "record", recordPath, join(dir, target)).status, 0);
    return JSON.parse(readFileSync(recordPath, "utf8")).models[join(dir, target)].surface["harness a"];
  };
  assert.equal(guards({ "main.rs": "#[cfg(e)] mod outer {\n    #![cfg(f)]\n    mod proofs;\n}\n", "outer/proofs.rs": harness }, "outer/proofs.rs"), "cfg(e) cfg(f)");
  assert.equal(guards({ "stray.rs": "#[cfg(g)] mod proofs;\n", "stray/Cargo.toml": "", "stray/lib.rs": "mod proofs;\n", "stray/proofs.rs": harness }, "stray/proofs.rs"), "");
  assert.equal(guards({ "mod.rs": "fn open() {\n", "loose/proofs.rs": harness }, "loose/proofs.rs"), "");

  const broken = crate({ "lib.rs": "mod proofs;\nfn open() {\n", "proofs.rs": harness });
  const failed = baseline(broken, "record", join(broken, "record.json"), join(broken, "proofs.rs"));
  assert.equal(failed.status, 1);
  assert.match(failed.stdout, new RegExp(`^FAIL baseline: ${join(broken, "lib.rs")}: unbalanced \\{`));
});

test("a cfg after an attribute that holds fn or mod is read up to the item's own keyword", () => {
  const harness = ({ rust: path }) => writeFileSync(path, "#[cfg_attr(any(), doc(fn x))]\n#[kani::proof]\nfn first() {}\n");
  const added = recordedThenEdited(harness, "rust", rust("#[kani::proof]", '#[cfg(feature = "slow-proofs")]\n#[kani::proof]'));
  assertChanged(added, "rust", "changed harness first", 'new: cfg(feature = "slow-proofs")');
  const module = ({ rust: path }) => writeFileSync(path, "#[cfg_attr(any(), doc(mod y))]\n#[cfg(b)]\nmod m {\n    #[kani::proof]\n    fn a() {}\n}\n");
  assertChanged(recordedThenEdited(module, "rust", rust("#[cfg(b)]\n", "")), "rust", "changed harness m::a", "old: cfg(b)");
  const files = models();
  const proofs = join(files.dir, "kani/proofs.rs");
  writeFileSync(files.rust, "#[cfg_attr(any(), doc(mod proofs))]\n#[cfg(c)]\nmod proofs;\n");
  writeFileSync(proofs, "#[kani::proof]\nfn a() {}\n");
  assert.equal(baseline(files.dir, "record", files.record, proofs).status, 0);
  assert.equal(JSON.parse(readFileSync(files.record, "utf8")).models[proofs].surface["harness a"], "cfg(c)");
  const outer = join(files.dir, "kani/outer/proofs.rs");
  mkdirSync(join(files.dir, "kani/outer"));
  writeFileSync(files.rust, "#[doc(mod q)]\n#[cfg(o)]\nmod outer {\n    #[cfg(c)]\n    mod proofs;\n}\n");
  writeFileSync(outer, "#[kani::proof]\nfn a() {}\n");
  assert.equal(baseline(files.dir, "record", files.record, outer).status, 0);
  assert.equal(JSON.parse(readFileSync(files.record, "utf8")).models[outer].surface["harness a"], "cfg(o) cfg(c)");
});

test("a cfg on a #[path] declaration or in another crate root that leads to a Kani harness file is changed", () => {
  const crate = (files) => {
    const dir = realpathSync(fixture());
    for (const [name, text] of Object.entries(files)) {
      mkdirSync(join(dir, name, ".."), { recursive: true });
      writeFileSync(join(dir, name), text);
    }
    return dir;
  };
  const harness = "#[kani::proof]\nfn a() { kani::cover!(true); }\n";
  const recorded = (files, target) => {
    const dir = crate(files);
    const result = baseline(dir, "record", join(dir, "record.json"), join(dir, target));
    return { dir, result, record: join(dir, "record.json") };
  };
  const guards = (files, target) => {
    const { dir, result, record } = recorded(files, target);
    assert.equal(result.status, 0, result.stdout);
    return JSON.parse(readFileSync(record, "utf8")).models[join(dir, target)].surface["harness a"];
  };

  const repro = recorded({ "lib.rs": '#[path = "checks.rs"]\nmod proofs;\n', "checks.rs": harness }, "checks.rs");
  assert.equal(repro.result.status, 0, repro.result.stdout);
  edit(join(repro.dir, "lib.rs"), "mod proofs;", '#[cfg(feature = "slow")]\nmod proofs;');
  const added = baseline(repro.dir, "compare", repro.record);
  assert.equal(added.status, 1);
  assert.deepEqual(lines(added), [`CHANGED ${join(repro.dir, "checks.rs")}`, "  changed harness a", "    old: ", '    new: cfg(feature = "slow")', "SUMMARY 0 unchanged, 1 changed"]);

  assert.equal(guards({ "lib.rs": '#[path = "x.rs"] mod y;\n', "x.rs": "#[cfg(c)] mod z;\n", "z.rs": harness }, "z.rs"), "cfg(c)");
  assert.equal(guards({ "lib.rs": "mod a;\n", "a.rs": '#[cfg(b)] #[path = "d"] mod m {\n    mod q;\n}\n', "d/q.rs": harness }, "d/q.rs"), "cfg(b)");
  assert.equal(guards({ "lib.rs": "mod a;\n", "a.rs": 'mod m {\n    #[cfg(e)] #[path = "p.rs"] mod p;\n}\n', "a/m/p.rs": harness }, "a/m/p.rs"), "cfg(e)");
  assert.equal(guards({ "lib.rs": '#[cfg_attr(feature = "x", path = "other.rs")]\nmod proofs;\n', "proofs.rs": harness, "other.rs": "" }, "proofs.rs"), 'cfg_attr(feature = "x", path = "other.rs")');
  assert.equal(guards({ "lib.rs": '#[path = "lib.rs"]\nmod again;\n#[cfg(w)] mod proofs;\n', "proofs.rs": harness }, "proofs.rs"), "cfg(w)");
  assert.equal(guards({ "lib.rs": "mod other;\nmod proofs;\n", "other.rs": "fn open() {\n", "proofs.rs": harness }, "proofs.rs"), "");

  const cargo = { "Cargo.toml": '[package]\nname = "p"\nversion = "0.1.0"\n', "src/lib.rs": "" };
  assert.equal(guards({ ...cargo, "tests/kani/main.rs": "#[cfg(t)] mod proofs;\n", "tests/kani/proofs.rs": harness }, "tests/kani/proofs.rs"), "cfg(t)");
  assert.equal(guards({ ...cargo, "src/bin/tool/main.rs": "#[cfg(u)] mod proofs;\n", "src/bin/tool/proofs.rs": harness }, "src/bin/tool/proofs.rs"), "cfg(u)");
  const library = { "Cargo.toml": "[package]\nname = \"p\"\nversion = \"0.1.0\"\n\n[lib]\npath = 'code/root.rs'\n", "code/root.rs": "#[cfg(v)] mod proofs;\n", "code/proofs.rs": harness };
  assert.equal(guards(library, "code/proofs.rs"), "cfg(v)");
  assert.equal(guards({ "Cargo.toml": "[workspace]\nmembers = []\n", "crates/foo/lib.rs": "#[cfg(w)] mod proofs;\n", "crates/foo/proofs.rs": harness }, "crates/foo/proofs.rs"), "cfg(w)");
  assert.equal(guards({ ...cargo, "src/main.rs": `#[cfg(z)] #[path = "lib.rs"] mod lib;\nfn main() { let path = "lib.rs"; }\n`, "src/lib.rs": harness }, "src/lib.rs"), "routes(lib.rs: unguarded; main.rs: cfg(z))");
  assert.equal(guards({ ...cargo, "src/main.rs": `fn main() { let path = "lib.rs"; }\n`, "src/lib.rs": harness }, "src/lib.rs"), "");
  assert.equal(guards({ "lib.rs": "mod a;\ncfg_if::cfg_if! { if #[cfg(unix)] { mod sys; } }\n", "sys.rs": "", "a.rs": "#[cfg(s)] mod sys;\n", "a/sys.rs": harness }, "a/sys.rs"), "cfg(s)");
  assert.equal(guards({ "lib.rs": "#[cfg(m)] mod r#match;\n", "match/mod.rs": harness }, "match/mod.rs"), "cfg(m)");
  assert.equal(guards({ "lib.rs": 'mod proofs;\n#[path = "sys\\\\win.rs"] mod sys;\n', "proofs.rs": harness }, "proofs.rs"), "");

  const hidden = recorded({ "lib.rs": "cfg_if::cfg_if! {\n    if #[cfg(kani)] {\n        mod proofs;\n    }\n}\n", "proofs.rs": harness }, "proofs.rs");
  assert.equal(hidden.result.status, 1);
  assert.match(hidden.result.stdout, new RegExp(`^FAIL baseline: ${join(hidden.dir, "lib.rs")}:3: a module declaration inside a macro or function body may load ${join(hidden.dir, "proofs.rs")}`));
  const wrapped = recorded({ "lib.rs": "mod proofs;\n", "proofs.rs": harness }, "proofs.rs");
  writeFileSync(join(wrapped.dir, "lib.rs"), "cfg_if::cfg_if! { if #[cfg(feature = \"slow\")] { mod proofs; } }\n");
  const failed = baseline(wrapped.dir, "compare", wrapped.record);
  assert.equal(failed.status, 1);
  assert.equal(lines(failed)[0], `CHANGED ${join(wrapped.dir, "proofs.rs")}`);
  assert.match(lines(failed)[1], /^ {2}FAIL .*lib\.rs:1: a module declaration inside a macro/);
  const pathed = recorded({ "lib.rs": 'fn f() {\n    #[path = "checks.rs"] mod proofs;\n}\n', "checks.rs": harness }, "checks.rs");
  assert.match(pathed.result.stdout, /lib\.rs:2: a module declaration inside a macro or function body/);
  const quiet = recorded({ "lib.rs": 'mod a;\n#[path = "a/proofs.rs"] mod p2;\n', "a.rs": "cfg_if::cfg_if! { if #[cfg(x)] { mod proofs; } }\n", "a/proofs.rs": harness }, "a/proofs.rs");
  assert.match(quiet.result.stdout, /a\.rs:1: a module declaration inside a macro or function body/);
  const stray = recorded({ "lib.rs": "", "stray.rs": harness }, "stray.rs");
  assert.equal(stray.result.status, 1);
  assert.match(stray.result.stdout, new RegExp(`^FAIL baseline: ${join(stray.dir, "stray.rs")}: no module declaration that the record can read leads to this file from a crate root`));
});

test("removing or guarding one of several routes to a Kani harness file is changed", () => {
  const harness = "#[kani::proof]\nfn a() { kani::cover!(true); }\n";
  const recorded = (files, target = "src/proofs.rs") => {
    const dir = realpathSync(fixture());
    for (const [name, text] of Object.entries({ "Cargo.toml": '[package]\nname = "p"\nversion = "0.1.0"\n', ...files, [target]: harness })) {
      mkdirSync(join(dir, name, ".."), { recursive: true });
      writeFileSync(join(dir, name), text);
    }
    const record = join(dir, "record.json");
    const proofs = join(dir, target);
    assert.equal(baseline(dir, "record", record, proofs).status, 0);
    return { dir, record, proofs, guards: JSON.parse(readFileSync(record, "utf8")).models[proofs].surface["harness a"] };
  };
  const compared = ({ dir, record }) => {
    const result = baseline(dir, "compare", record);
    assert.equal(result.status, 1, result.stdout);
    return lines(result);
  };

  const both = { "src/lib.rs": "mod proofs;\n", "src/main.rs": '#[cfg(feature = "slow")]\nmod proofs;\nfn main() {}\n' };
  const removed = recorded(both);
  assert.equal(removed.guards, 'routes(lib.rs: unguarded; main.rs: cfg(feature = "slow"))');
  writeFileSync(join(removed.dir, "src/lib.rs"), "");
  assert.deepEqual(compared(removed), [`CHANGED ${removed.proofs}`, "  changed harness a", '    old: routes(lib.rs: unguarded; main.rs: cfg(feature = "slow"))', '    new: cfg(feature = "slow")', "SUMMARY 0 unchanged, 1 changed"]);

  const guarded = recorded(both);
  edit(join(guarded.dir, "src/lib.rs"), "mod proofs;", "#[cfg(x)] mod proofs;");
  assert.deepEqual(compared(guarded).slice(2, 4), ['    old: routes(lib.rs: unguarded; main.rs: cfg(feature = "slow"))', '    new: routes(lib.rs: cfg(x); main.rs: cfg(feature = "slow"))']);

  const swapped = recorded(both);
  writeFileSync(join(swapped.dir, "src/lib.rs"), '#[cfg(feature = "slow")]\nmod proofs;\n');
  writeFileSync(join(swapped.dir, "src/main.rs"), "mod proofs;\nfn main() {}\n");
  assert.deepEqual(compared(swapped).slice(2, 4), ['    old: routes(lib.rs: unguarded; main.rs: cfg(feature = "slow"))', '    new: routes(lib.rs: cfg(feature = "slow"); main.rs: unguarded)']);

  const replaced = recorded(both);
  writeFileSync(join(replaced.dir, "src/lib.rs"), "");
  mkdirSync(join(replaced.dir, "tests"));
  writeFileSync(join(replaced.dir, "tests/t.rs"), '#[path = "../src/proofs.rs"]\nmod proofs;\n');
  assert.deepEqual(compared(replaced).slice(2, 4), ['    old: routes(lib.rs: unguarded; main.rs: cfg(feature = "slow"))', '    new: routes(../tests/t.rs: unguarded; main.rs: cfg(feature = "slow"))']);

  const twice = recorded({ "src/lib.rs": "mod proofs;\n", "src/main.rs": "mod proofs;\nfn main() {}\n" });
  assert.equal(twice.guards, "routes(lib.rs: unguarded; main.rs: unguarded)");
  writeFileSync(join(twice.dir, "src/main.rs"), "fn main() {}\n");
  assert.deepEqual(compared(twice).slice(2, 4), ["    old: routes(lib.rs: unguarded; main.rs: unguarded)", "    new: "]);

  const root = recorded({ "src/lib.rs": "mod proofs;\n", "src/main.rs": '#[cfg(z)] #[path = "lib.rs"] mod lib;\nfn main() {}\n' });
  assert.equal(root.guards, "routes(lib.rs: unguarded; main.rs: cfg(z))");

  const module = recorded({ "src/lib.rs": '#[cfg(feature = "x")] mod a;\n', "src/a/mod.rs": "mod main;\n", "src/a/main.rs": "mod proofs;\n" }, "src/a/main/proofs.rs");
  assert.equal(module.guards, 'cfg(feature = "x")');
});

test("a route to a Kani harness file through include! is followed, and one that a macro may build fails the record", () => {
  const harness = "#[kani::proof]\nfn a() { kani::cover!(true); }\n";
  const recorded = (files, target) => {
    const dir = realpathSync(fixture());
    for (const [name, text] of Object.entries({ ...files, [target]: harness })) {
      mkdirSync(join(dir, name, ".."), { recursive: true });
      writeFileSync(join(dir, name), text);
    }
    const record = join(dir, "record.json");
    const result = baseline(dir, "record", record, join(dir, target));
    const guards = () => JSON.parse(readFileSync(record, "utf8")).models[join(dir, target)].surface["harness a"];
    return { dir, record, result, guards };
  };
  const guards = (files, target) => {
    const { result, guards: read } = recorded(files, target);
    assert.equal(result.status, 0, result.stdout);
    return read();
  };
  const failure = (files, target) => {
    const { result } = recorded(files, target);
    assert.equal(result.status, 1, result.stdout);
    return result.stdout;
  };

  const included = recorded({ "lib.rs": '#[path = "sub/proofs.rs"] mod proofs;\ninclude!("sub/items.rs");\n', "sub/items.rs": '#[path = "proofs.rs"] mod again;\n' }, "sub/proofs.rs");
  assert.equal(included.result.status, 0, included.result.stdout);
  assert.equal(included.guards(), "routes(../lib.rs: unguarded; ../lib.rs: unguarded)");
  edit(join(included.dir, "lib.rs"), "include!", '#[cfg(feature = "slow")] include!');
  const switched = baseline(included.dir, "compare", included.record);
  assert.equal(switched.status, 1, switched.stdout);
  assert.deepEqual(lines(switched).slice(2, 4), ["    old: routes(../lib.rs: unguarded; ../lib.rs: unguarded)", '    new: routes(../lib.rs: unguarded; ../lib.rs: cfg(feature = "slow"))']);

  assert.equal(guards({ "lib.rs": '#![cfg(f)]\n#[cfg(x)] include!("sub/items.rs");\n', "sub/items.rs": "#[cfg(y)] mod q;\n" }, "sub/q.rs"), "cfg(f) cfg(x) cfg(y)");
  assert.equal(guards({ "lib.rs": '#[cfg(m)] mod m {\n    include!("items.rs");\n}\n', "items.rs": "mod q;\n" }, "q.rs"), "cfg(m)");
  assert.equal(guards({ "lib.rs": "mod a;\n", "a.rs": 'include!("sub/one.rs");\n', "sub/one.rs": 'include!("two.rs");\n', "sub/two.rs": "#[cfg(t)] mod q;\n" }, "sub/q.rs"), "cfg(t)");
  assert.equal(guards({ "lib.rs": 'mod proofs;\nconst SOURCE: &str = include_str!("proofs.rs");\nfn f() { let _ = include_bytes!("proofs.rs"); }\n' }, "proofs.rs"), "");
  assert.equal(guards({ "lib.rs": 'mod proofs;\ninclude!(concat!(env!("OUT_DIR"), "/bindings.rs"));\n' }, "proofs.rs"), "");
  assert.match(failure({ "lib.rs": 'mod proofs;\ninclude!(concat!(env!("OUT_DIR"), "/proofs.rs"));\n' }, "proofs.rs"), /lib\.rs:2: cannot read the path in 'include!\(concat!/);

  const macro = 'mod proofs;\nmacro_rules! load { ($m:ident, $p:literal) => { #[path = $p] mod $m; } }\nload!(again, "proofs.rs");\n';
  assert.match(failure({ "lib.rs": macro }, "proofs.rs"), /^FAIL baseline: .*lib\.rs:3: a macro invocation may build a module declaration that loads .*proofs\.rs/);
  const named = '#[path = "proofs.rs"] mod readable;\nmacro_rules! declare {\n    ($m:ident) => { mod $m; };\n}\ndeclare!(proofs);\n';
  assert.match(failure({ "lib.rs": named }, "proofs.rs"), /lib\.rs:5: a macro invocation may build a module declaration that loads/);
  assert.equal(guards({ "lib.rs": "mod proofs;\nmacro_rules! declare {\n    ($m:ident) => { mod $m; };\n}\ndeclare!(other);\n", "other.rs": "" }, "proofs.rs"), "");
  const unread = /lib\.rs:2: an invocation of a macro that the record cannot read may build a module declaration that loads .*proofs\.rs/;
  assert.match(failure({ "lib.rs": '#[path = "proofs.rs"] mod readable;\nbuilders::declare!(proofs);\n' }, "proofs.rs"), unread);
  assert.match(failure({ "lib.rs": '#[path = "proofs.rs"] mod readable;\nuse builders::declare; declare! { proofs }\n' }, "proofs.rs"), unread);
  assert.match(failure({ "lib.rs": '#[path = "proofs.rs"] mod readable;\nbuilders::declare!(proofs);\nmacro_rules! declare { ($m:ident) => { struct $m; } }\n' }, "proofs.rs"), unread);
  assert.equal(guards({ "lib.rs": "mod proofs;\nbuilders::declare!(other);\nfn f() { builders::declare!(proofs); }\n" }, "proofs.rs"), "");
  assert.equal(guards({ "lib.rs": "mod proofs;\nmacro_rules! mark { ($m:ident) => { const _: () = (); } }\nmark!(proofs);\ncrate::mark!(proofs);\n" }, "proofs.rs"), "");
  assert.match(failure({ "lib.rs": '#[path = "proofs.rs"] mod readable;\nbuilders::declare!(mod proofs);\n' }, "proofs.rs"), unread);
  assert.match(failure({ "lib.rs": "mod proofs;\nbuilders::declare!(proofs);\n" }, "proofs.rs"), /if the macro declares no module, keep the module's name out of the invocation or rename the module/);
  const forwarded = /lib\.rs:3: an invocation of a macro that the record cannot read may build a module declaration that loads .*proofs\.rs/;
  assert.match(failure({ "lib.rs": '#[path = "proofs.rs"] mod readable;\nmacro_rules! wrap { ($m:ident) => { builders::declare!($m); } }\nwrap!(proofs);\n' }, "proofs.rs"), forwarded);
  assert.match(failure({ "lib.rs": '#[path = "proofs.rs"] mod readable;\nmacro_rules! inner { ($m:ident) => { builders::declare!($m); } }\nmacro_rules! outer { ($m:ident) => { inner!($m); } }\nouter!(proofs);\n' }, "proofs.rs"), /lib\.rs:4: an invocation of a macro that the record cannot read/);
  assert.match(failure({ "lib.rs": '#[path = "proofs.rs"] mod readable;\nmacro_rules! wrap { () => { builders::declare!(proofs); }; }\nwrap!();\n' }, "proofs.rs"), unread);
  assert.match(failure({ "lib.rs": '#[path = "proofs.rs"] mod readable;\nmacro_rules! wrap { ($($t:tt)*) => { $($t)* } }\nwrap! { builders::declare!(proofs); }\n' }, "proofs.rs"), forwarded);
  assert.equal(guards({ "lib.rs": "mod proofs;\nmacro_rules! mark { ($m:ident) => { thread_local!(static X: u8 = 0); struct $m; } }\nmark!(proofs);\n" }, "proofs.rs"), "");
  assert.equal(guards({ "lib.rs": 'mod proofs;\nmacro_rules! named { ($m:ident) => { fn $m() { println!("{}", stringify!($m)); } } }\nnamed!(proofs);\n' }, "proofs.rs"), "");
  assert.equal(guards({ "lib.rs": 'mod proofs;\nstruct S;\nimpl S { fn f() { let proofs = 0; println!("{}", proofs); } }\n' }, "proofs.rs"), "");
  const chained = '#[path = "proofs.rs"] mod readable;\nmacro_rules! declare { ($m:ident) => { mod $m; } }\nmacro_rules! outer { ($m:ident) => { declare!($m); } }\nouter!(proofs);\n';
  assert.match(failure({ "lib.rs": chained }, "proofs.rs"), /lib\.rs:4: an invocation of a macro that the record cannot read/);
  assert.match(failure({ "lib.rs": '#[path = "proofs.rs"] mod readable;\nmacro_rules! declare { ($m:ident) => { mod $m; } }\nmacro_rules! wrap { ($($t:tt)*) => { $($t)* } }\nwrap! { declare!(proofs); }\n' }, "proofs.rs"), /lib\.rs:4: a macro invocation may build a module declaration that loads/);
  const checked = { "Cargo.toml": '[package]\nname = "p"\nversion = "0.1.0"\n', "src/lib.rs": "mod queue;\n", "tests/suite.rs": "macro_rules! suite {\n    ($m:ident) => { mod $m { #[test] fn works() { assert!($m::CAP > 0); } } };\n}\nsuite!(queue);\n" };
  assert.equal(guards(checked, "src/queue.rs"), "");
  const helpers = "macro_rules! len { ($proofs:expr, $n:expr) => { assert_eq!($proofs.len(), $n) }; }\nmacro_rules! empty { ($q:expr) => {{ let proofs = $q; assert!(proofs.is_empty()); }}; }\nmacro_rules! show { () => { println!(\"{}\", proofs) }; }\n";
  assert.equal(guards({ "lib.rs": `mod proofs;\n${helpers}` }, "proofs.rs"), "");
  assert.equal(guards({ "lib.rs": "mod proofs;\nmacro_rules! m { ($name:ident, $c:expr) => { const _: () = if !($c) { panic!() }; pub struct $name; }; }\nm!(proofs, true);\n" }, "proofs.rs"), "");
  assert.equal(guards({ "lib.rs": "mod proofs;\nmacro_rules! check { ($name:ident, $e:expr) => { const _: () = assert!($e); pub struct $name; }; }\ncheck!(proofs, 1 > 0);\n" }, "proofs.rs"), "");
  assert.equal(guards({ "lib.rs": 'mod proofs;\nmacro_rules! suite { ($name:ident) => { #[doc = concat!("Tests for ", stringify!($name))] mod $name {} }; }\nsuite!(proofs);\n' }, "proofs.rs"), "");
  assert.match(failure({ "lib.rs": '#[path = "proofs.rs"] mod readable;\nmacro_rules! wrap { (fn $m:ident) => { builders::declare!($m); }; }\nwrap!(fn proofs);\n' }, "proofs.rs"), forwarded);
  const callback = "mod proofs;\nmacro_rules! strip { ($mac:ident!($($t:tt)*)) => { $mac!([] $($t)*); }; }\nmacro_rules! shape {\n    ([] struct $name:ident { $($f:tt)* }) => { struct $name { $($f)* } };\n    ($($t:tt)*) => { strip!(shape!($($t)*)); };\n}\nshape! { struct S { proofs: u8 } }\n";
  assert.equal(guards({ "lib.rs": callback }, "proofs.rs"), "");
  const local = "macro_rules! declare { ($m:ident) => { struct $m; } }\n";
  assert.match(failure({ "lib.rs": '#[path = "proofs.rs"] mod readable;\nmod other;\nuse builders::declare;\ndeclare!(proofs);\n', "other.rs": local }, "proofs.rs"), /lib\.rs:4: an invocation of a macro that the record cannot read/);
  assert.match(failure({ "lib.rs": `#[path = "proofs.rs"] mod readable;\nmod m { ${local}}\nuse builders::declare;\ndeclare!(proofs);\n` }, "proofs.rs"), /lib\.rs:5: an invocation of a macro that the record cannot read/);
  assert.match(failure({ "lib.rs": `#[path = "proofs.rs"] mod readable;\nuse builders::declare;\nmod a;\n${local}`, "a.rs": "declare!(proofs);\n" }, "proofs.rs"), /a\.rs:1: an invocation of a macro that the record cannot read/);
  assert.equal(guards({ "lib.rs": "mod proofs;\n#[macro_use]\nmod other;\ndeclare!(proofs);\n", "other.rs": local }, "proofs.rs"), "");
  assert.equal(guards({ "lib.rs": `mod proofs;\n#[macro_use] mod m { ${local}}\ndeclare!(proofs);\n` }, "proofs.rs"), "");
  assert.equal(guards({ "lib.rs": `mod proofs;\n${local}mod a;\n`, "a.rs": "mod b;\n", "a/b.rs": "declare!(proofs);\n" }, "proofs.rs"), "");
  assert.equal(guards({ "lib.rs": 'mod proofs;\ninclude!("defs.rs");\ndeclare!(proofs);\n', "defs.rs": local }, "proofs.rs"), "");
  const exported = "#[macro_export]\nmacro_rules! declare { ($m:ident) => { struct $m; } }\n";
  assert.match(failure({ "lib.rs": '#[path = "proofs.rs"] mod readable;\nmod a;\n#[macro_export]\nmacro_rules! declare { ($m:ident) => { builders::declare!($m); } }\ncrate::declare!(proofs);\n', "a.rs": local }, "proofs.rs"), /lib\.rs:5: an invocation of a macro that the record cannot read/);
  const callsite = { "lib.rs": '#[path = "a/proofs.rs"] mod readable;\nmacro_rules! inner { ($m:ident) => { struct $m; } }\nmacro_rules! wrap { ($m:ident) => { inner!($m); } }\nmod a;\n', "a.rs": "macro_rules! inner { ($m:ident) => { builders::declare!($m); } }\nwrap!(proofs);\n" };
  assert.match(failure(callsite, "a/proofs.rs"), /a\.rs:2: an invocation of a macro that the record cannot read/);
  assert.equal(guards({ "lib.rs": "macro_rules! wrap { ($m:ident) => { inner!($m); } }\nmod a;\n", "a.rs": `mod proofs;\nmacro_rules! inner { ($m:ident) => { struct $m; } }\nwrap!(proofs);\n` }, "a/proofs.rs"), "");
  assert.match(failure({ "lib.rs": '#[path = "proofs.rs"] mod readable;\nmod defs;\nmod x { use crate::declare; }\nmod y { use builders::declare; declare!(proofs); }\n', "defs.rs": exported }, "proofs.rs"), /lib\.rs:4: an invocation of a macro that the record cannot read/);
  assert.equal(guards({ "lib.rs": "mod proofs;\nmod defs;\ndeclare!(proofs);\n", "defs.rs": `#![macro_use]\n${local}` }, "proofs.rs"), "");
  assert.equal(guards({ "lib.rs": "mod proofs;\nmod defs;\ndeclare!(proofs);\n", "defs.rs": exported }, "proofs.rs"), "");
  const attributed = /lib\.rs:2: an attribute macro that the record cannot read may build a module declaration that loads .*proofs\.rs/;
  assert.match(failure({ "lib.rs": '#[path = "proofs.rs"] mod readable;\n#[builders::declare(proofs)]\nstruct S;\n' }, "proofs.rs"), attributed);
  assert.match(failure({ "lib.rs": '#[path = "proofs.rs"] mod readable;\n#[declare(proofs)]\nstruct S;\nuse builders::declare;\n' }, "proofs.rs"), attributed);
  assert.match(failure({ "lib.rs": '#[path = "proofs.rs"] mod readable;\n#[cfg_attr(feature = "x", builders::declare(proofs))]\nstruct S;\n' }, "proofs.rs"), attributed);
  assert.match(failure({ "lib.rs": '#[path = "proofs.rs"] mod readable;\nmod m {\n    #[builders::declare(proofs)]\n    struct S;\n}\n' }, "proofs.rs"), /lib\.rs:3: an attribute macro that the record cannot read/);
  assert.match(failure({ "lib.rs": "mod proofs;\n#[builders::declare(proofs)]\nstruct S;\n" }, "proofs.rs"), /if the attribute declares no module, keep the module's name out of its arguments or rename the module/);
  const inert = 'mod proofs;\n#![allow(dead_code)]\n#[derive(Clone)]\n#[repr(C)]\npub struct Proofs;\n#[cfg_attr(test, derive(Debug))]\n#[doc = "proofs"]\n#[builders::declare(other, proofs::Item)]\nstruct T { #[serde(rename = "x")] proofs: u8 }\nimpl T { #[builders::declare(proofs)] fn f() {} }\nfn g() { #[builders::declare(proofs)] let x = 1; }\n#[kani::proof]\n#[cfg(proofs)]\nfn h() {}\n';
  assert.equal(guards({ "lib.rs": inert }, "proofs.rs"), "");
  const derived = 'mod proofs;\n#[derive(Clone)]\n#[helper(proofs)]\nstruct S;\n#[cfg_attr(feature = "x", derive(Bake))]\n#[cfg_attr(feature = "x", databake(path = proofs))]\nstruct T;\n#[tracing::instrument(skip(proofs))]\nfn f(proofs: u8) {}\n';
  assert.equal(guards({ "lib.rs": derived }, "proofs.rs"), "");
  assert.equal(guards({ "lib.rs": "mod proofs;\nstruct Tuple(#[builders::declare(proofs)] u8, #[into(proofs)] u16);\n" }, "proofs.rs"), "");
  assert.match(failure({ "lib.rs": '#[path = "proofs.rs"] mod readable;\n#[derive(Clone)]\n#[builders::declare(proofs)]\nstruct S;\n' }, "proofs.rs"), /lib\.rs:3: an attribute macro that the record cannot read/);
  const recursive = "mod proofs;\nmod t {\n    macro_rules! make { ($m:ident) => { struct $m; }; ($m:ident, $n:ident) => { make!($m); make!($n); }; }\n    make!(proofs, other);\n}\n";
  assert.equal(guards({ "lib.rs": recursive }, "proofs.rs"), "");
  assert.equal(guards({ "lib.rs": `mod proofs;\nmod a;\n${local}declare!(proofs);\n`, "a.rs": "macro_rules! declare { ($m:ident) => { builders::declare!($m); } }\n" }, "proofs.rs"), "");
  assert.equal(guards({ "lib.rs": "mod proofs;\n#[macro_use] mod defs;\nmod a;\n", "defs.rs": "#[macro_export]\nmacro_rules! declare { ($m:ident) => { struct $m; } }\n", "a.rs": "use crate::declare;\ndeclare!(proofs);\n" }, "proofs.rs"), "");
  assert.equal(guards({ "lib.rs": "mod proofs;\nmod defs;\nmod a;\n", "defs.rs": "#[macro_export]\nmacro_rules! declare { ($m:ident) => { struct $m; } }\n", "a.rs": "use crate::declare;\ndeclare!(proofs);\n" }, "proofs.rs"), "");
  const pointer = '#[path = "outer/proofs.rs"] mod readable;\nmacro_rules! wrap { ($m:ident) => { pub struct S { pub f: fn() } pub mod outer { builders::declare!($m); } }; }\nwrap!(proofs);\n';
  assert.match(failure({ "lib.rs": pointer }, "outer/proofs.rs"), /lib\.rs:3: an invocation of a macro that the record cannot read/);
  const uses = "mod queue;\nconst _: () = assert!(queue::CAP > 0);\ncfg_if::cfg_if! { if #[cfg(feature = \"std\")] { pub use queue::Queue; } }\n";
  assert.equal(guards({ "lib.rs": uses + "proptest::proptest! { #[test] fn push(x in 0u8..4) { let queue = x; let _ = self.queue; } }\n" }, "queue.rs"), "");
  assert.equal(guards({ "lib.rs": '#[cfg(kani)] mod kani;\ncfg_if::cfg_if! { if #[cfg(kani)] { const K: u8 = 1; } }\n' }, "kani/mod.rs"), "");
  const nested = '#[path = "m/proofs.rs"] mod readable;\ncfg_if::cfg_if! {\n    if #[cfg(x)] {\n        mod m {\n            mod proofs;\n        }\n    }\n}\n';
  assert.match(failure({ "lib.rs": nested }, "m/proofs.rs"), /lib\.rs:5: a module declaration inside a macro or function body may load/);
  assert.equal(guards({ "lib.rs": nested.replace("mod m {", "mod n {"), "n/proofs.rs": "" }, "m/proofs.rs"), "");

  const suite = { "Cargo.toml": '[package]\nname = "p"\nversion = "0.1.0"\n', "src/lib.rs": "mod queue;\n", "tests/suite.rs": "macro_rules! suite {\n    ($m:ident) => { mod $m { #[test] fn works() {} } };\n}\nsuite!(queue);\n" };
  assert.equal(guards(suite, "src/queue.rs"), "");
  assert.equal(guards({ "lib.rs": 'mod proofs;\npub fn harness_path() -> String { format!("{}/proofs.rs", env!("CARGO_MANIFEST_DIR")) }\n' }, "proofs.rs"), "");
  const items = { "sub/items.rs": '#[path = "proofs.rs"] mod again;\n' };
  const wrapped = '#[path = "sub/proofs.rs"] mod proofs;\nmacro_rules! wrap { ($($t:tt)*) => { $($t)* } }\nwrap! { include!("sub/items.rs"); }\n';
  assert.match(failure({ "lib.rs": wrapped, ...items }, "sub/proofs.rs"), /lib\.rs:3: an include! inside a macro or function body reads a file that may load/);
  assert.equal(guards({ "lib.rs": wrapped, "sub/items.rs": "mod other;\n", "sub/other.rs": "" }, "sub/proofs.rs"), "");
  assert.equal(guards({ "lib.rs": '#[path = "sub/proofs.rs"] mod proofs;\n#[cfg(b)] include! { "sub/items.rs" }\n', ...items }, "sub/proofs.rs"), "routes(../lib.rs: unguarded; ../lib.rs: cfg(b))");

  const manifest = 'include!(concat!(env!("CARGO_MANIFEST_DIR"), "/sub/items.rs"));\n';
  const cargo = { "Cargo.toml": '[package]\nname = "p"\nversion = "0.1.0"\n', ...items };
  const computed = recorded({ ...cargo, "lib.rs": `#[path = "sub/proofs.rs"] mod proofs;\n${manifest}` }, "sub/proofs.rs");
  assert.equal(computed.result.status, 0, computed.result.stdout);
  assert.equal(computed.guards(), "routes(../lib.rs: unguarded; ../lib.rs: unguarded)");
  writeFileSync(join(computed.dir, "lib.rs"), `#[path = "sub/proofs.rs"] mod proofs;\n#[cfg(feature = "slow")]\n${manifest}`);
  const guardedComputed = baseline(computed.dir, "compare", computed.record);
  assert.equal(guardedComputed.status, 1, guardedComputed.stdout);
  assert.deepEqual(lines(guardedComputed).slice(2, 4), ["    old: routes(../lib.rs: unguarded; ../lib.rs: unguarded)", '    new: routes(../lib.rs: unguarded; ../lib.rs: cfg(feature = "slow"))']);
  assert.equal(guards({ "lib.rs": '#[path = "sub/proofs.rs"] mod proofs;\n#[cfg(c)] include!(std::concat!("sub/", "items.rs",));\n', ...items }, "sub/proofs.rs"), "routes(../lib.rs: unguarded; ../lib.rs: cfg(c))");
  assert.match(failure({ ...cargo, "lib.rs": `#[path = "sub/proofs.rs"] mod proofs;\nfn f() { ${manifest.trim()} }\n` }, "sub/proofs.rs"), /lib\.rs:2: an include! inside a macro or function body reads a file that may load/);
  assert.match(failure({ ...items, "lib.rs": `#[path = "sub/proofs.rs"] mod proofs;\n${manifest}` }, "sub/proofs.rs"), /lib\.rs:2: cannot read the path in 'include!\(concat!.*\)': no Cargo\.toml above the crate root sets env!\("CARGO_MANIFEST_DIR"\)/);
  const macroManifest = `#[path = "sub/proofs.rs"] mod proofs;\nmacro_rules! items { ($($i:item)*) => { $($i)* } }\nitems! { ${manifest.trim()} }\n`;
  assert.match(failure({ ...items, "lib.rs": macroManifest }, "sub/proofs.rs"), /lib\.rs:3: an include! inside a macro or function body reads a file that may load/);
  const workspace = {
    "Cargo.toml": '[package]\nname = "p"\nversion = "0.1.0"\n\n[workspace]\nmembers = ["sub"]\n',
    "sub/Cargo.toml": '[package]\nname = "q"\nversion = "0.1.0"\n',
    "sub/src/lib.rs": "",
    "src/lib.rs": 'mod proofs;\ninclude!("../sub/shared.rs");\n',
    "sub/shared.rs": 'include!(concat!(env!("CARGO_MANIFEST_DIR"), "/src/items.rs"));\n',
    "src/items.rs": '#[path = "proofs.rs"] mod again;\n',
  };
  assert.equal(guards(workspace, "src/proofs.rs"), "routes(lib.rs: unguarded; lib.rs: unguarded)");
  assert.equal(guards({ "Cargo.toml": cargo["Cargo.toml"], "src/lib.rs": '#[cfg(kani)] mod tests;\n#[cfg(feature = "codegen")]\ninclude!("../tests/generated.rs");\n' }, "src/tests.rs"), "");
});

test("only a cfg_attr whose own attribute list applies cfg guards a Kani harness", () => {
  const docs = ({ rust: path }) => writeFileSync(path, '#[cfg_attr(docsrs, doc(cfg(feature = "x")))]\nmod proofs {\n    #[kani::proof]\n    fn a() { kani::cover!(true); }\n}\n');
  assertUnchanged(recordedThenEdited(docs, "rust", rust('feature = "x"', 'feature = "y"')), "rust");
  const guards = (attributes) => {
    const files = models();
    writeFileSync(files.rust, `${attributes}\n#[kani::proof]\nfn a() {}\n`);
    assert.equal(baseline(files.dir, "record", files.record, files.rust).status, 0);
    return JSON.parse(readFileSync(files.record, "utf8")).models[files.rust].surface["harness a"];
  };
  assert.equal(guards('#[cfg_attr(docsrs, doc(cfg(feature = "x")))]'), "");
  assert.equal(guards('#[cfg_attr(feature = "a,cfg(b)", doc(hidden))]'), "");
  assert.equal(guards("#[my(#[cfg(z)] q)]"), "");
  assert.equal(guards("#![my(#[cfg(z)] q)]"), "");
  assert.equal(guards("#[cfg_attr(a, doc(hidden), cfg(b))]"), "cfg_attr(a, doc(hidden), cfg(b))");
  assert.equal(guards("#[cfg_attr(a, cfg_attr(b, cfg(c)))]"), "cfg_attr(a, cfg_attr(b, cfg(c)))");
  assert.equal(guards("#[cfg_attr(a, cfg_attr(b, doc(cfg(c))))]"), "");
});

test("moving a Kani assumption from a helper into a harness changes its owner", () => {
  const outcome = recordedThenEdited(null, "rust", ({ rust: path }) => {
    edit(path, "        kani::assume(window > 0 && window <= 2);\n", "");
    edit(path, "        let (window, state) = inputs();", "        let (window, state) = inputs();\n        kani::assume(window > 0 && window <= 2);");
  });
  assertChanged(outcome, "rust", "removed assume window > 0 && window <= 2", "added assume window > 0 && window <= 2");
});

test("Kani items retain qualified owners when equal function names occur in nested modules", () => {
  const setup = ({ rust: path }) => writeFileSync(path, [
    "mod outer { mod a { #[kani::proof] fn same() { kani::assume(true); } }",
    "mod b { #[kani::proof] fn same() {} } }", "",
  ].join("\n"));
  const outcome = recordedThenEdited(setup, "rust", ({ rust: path }) => {
    edit(path, "fn same() { kani::assume(true); }", "fn same() {}");
    edit(path, "mod b { #[kani::proof] fn same() {}", "mod b { #[kani::proof] fn same() { kani::assume(true); }");
  });
  assertChanged(outcome, "rust", "removed assume true in outer::a::same", "added assume true in outer::b::same");
});

test("moving a Kani cover or stub between functions changes its owner", () => {
  for (const [first, second, kind] of [
    ["fn a() { kani::cover!(true); } fn b() {}", "fn a() {} fn b() { kani::cover!(true); }", "cover true"],
    ["#[kani::stub(real, fake)] fn a() {} fn b() {}", "fn a() {} #[kani::stub(real, fake)] fn b() {}", "stub real, fake"],
  ]) {
    const setup = ({ rust: path }) => writeFileSync(path, first);
    const outcome = recordedThenEdited(setup, "rust", ({ rust: path }) => writeFileSync(path, second));
    assertChanged(outcome, "rust", `removed ${kind} in a`);
  }
});

test("reordering functions with identical Kani assumptions preserves their owners", () => {
  const a = "fn a() { kani::assume(true); kani::assume(true); }";
  const b = "fn b() { kani::assume(true); }";
  const setup = ({ rust: path }) => writeFileSync(path, `${a}\n${b}\n`);
  assertUnchanged(recordedThenEdited(setup, "rust", ({ rust: path }) => writeFileSync(path, `${b}\n${a}\n`)), "rust");
  const removed = recordedThenEdited(setup, "rust", ({ rust: path }) => edit(path, a, "fn a() { kani::assume(true); }"));
  assertChanged(removed, "rust", "removed assume true in a #2");
});

test("conditional definitions with the same qualified name retain separate Kani owners", () => {
  const setup = ({ rust: path }) => writeFileSync(path, "#[cfg(a)] fn same() { kani::assume(true); } #[cfg(b)] fn same() {}");
  const outcome = recordedThenEdited(setup, "rust", ({ rust: path }) => {
    edit(path, "{ kani::assume(true); }", "{}");
    edit(path, "#[cfg(b)] fn same() {}", "#[cfg(b)] fn same() { kani::assume(true); }");
  });
  assertChanged(outcome, "rust", "removed assume true in same", "added assume true in same[2]");
});

test("duplicate assumptions cannot stand in for a constraint on a different function definition", () => {
  const setup = ({ rust: path }) => writeFileSync(path,
    "#[cfg(a)] fn same() { kani::assume(true); kani::assume(true); } #[cfg(b)] fn same() { kani::assume(true); }");
  const outcome = recordedThenEdited(setup, "rust", ({ rust: path }) => writeFileSync(path,
    "#[cfg(a)] fn same() { kani::assume(true); } #[cfg(b)] fn same() { kani::assume(true); kani::assume(true); }"));
  assertChanged(outcome, "rust", "added assume true in same");
});

test("generic free functions and local blocks retain their Kani owner", () => {
  const setup = ({ rust: path }) => writeFileSync(path, "mod m { pub unsafe fn r#type<'a, const N: usize>(x: &'a [u8; N]) { if N > 0 { kani::assume(x[0] > 0); } } }");
  const outcome = recordedThenEdited(setup, "rust", ({ rust: path }) => edit(path, "x[0] > 0", "x[0] > 1"));
  assertChanged(outcome, "rust", "removed assume x[0] > 0 in m::r#type");
});

test("a Kani form in an unsupported Rust owner fails instead of being recorded without context", () => {
  for (const source of [
    "impl State { fn helper() { kani::assume(true); } }",
    "trait T { fn helper() { kani::assume(true); } }",
    "macro_rules! body { () => { kani::assume(true); } }",
    "fn helper() { wrapper! { kani::assume(true); } }",
    "fn helper() { wrapper!(kani::assume(true)); }",
    "fn helper() { macro_rules! body { () => { kani::assume(true); } } }",
    "fn helper() { impl State { fn local() { kani::assume(true); } } }",
    "kani::assume(true);",
  ]) {
    const files = models();
    writeFileSync(files.rust, source);
    const result = baseline(files.dir, "record", files.record, files.rust);
    assert.equal(result.status, 1, source);
    assert.ok(result.stdout.includes("cannot identify a function owner"), result.stdout);
  }
});

const multiline = rust("kani::assume(window > 0 && window <= 2);", "kani::assume(\n            window > 0\n            && window <= 2,\n        );");

test("an edit to one line of a multi-line Kani assume is changed", () => {
  const outcome = recordedThenEdited(multiline, "rust", rust("&& window <= 2,", "&& window <= 3,"));
  assertChanged(outcome, "rust", "removed assume window > 0 && window <= 2,", "added assume window > 0 && window <= 3,");
});

test("a reformatted Kani assume is unchanged", () => {
  assertUnchanged(recordedThenEdited(multiline, "rust", rust("window > 0\n            && window <= 2,", "window > 0 && window <= 2,")), "rust");
});

test("whitespace inside Rust string literals is part of a Kani assumption", () => {
  for (const literal of ['"a b"', 'b"a b"', 'r##"a b"##', 'br#"a b"#', String.raw`r#"a \" b"#`, 'cr#"a " b " c"#']) {
    const value = literal.startsWith("cr") ? `${literal}.to_bytes()` : literal;
    const assumption = `kani::assume(${value}.len() == usize::from(window));`;
    const setup = rust("kani::assume(window > 0 && window <= 2);", assumption);
    assertChanged(recordedThenEdited(setup, "rust", rust(literal, literal.replace(" b", "  b"))), "rust", "removed assume", "added assume");
    assertUnchanged(recordedThenEdited(setup, "rust", rust(assumption, `kani::assume(\n    ${value}.len() == usize::from(window)\n);`)), "rust");
  }
});

test("a removed Kani cover is changed and an added cover is not", () => {
  assertChanged(recordedThenEdited(null, "rust", rust('        kani::cover!(state.next == state.consumed, "queue empty");\n', "")), "rust", 'removed cover state.next == state.consumed, "queue empty"');
  assertUnchanged(recordedThenEdited(null, "rust", rust("        if let Some(after) = consume(state) {", '        kani::cover!(state.next == 3, "three");\n        if let Some(after) = consume(state) {')), "rust");
});

test("a removed Kani harness is changed", () => {
  const remove = rust("    #[kani::proof]\n    #[kani::unwind(2)]\n    fn consume_keeps_invariant", "    #[kani::unwind(2)]\n    fn consume_keeps_invariant");
  assertChanged(recordedThenEdited(null, "rust", remove), "rust", "removed harness proofs::consume_keeps_invariant");
});

test("a Kani body edit that touches no assume, cover, stub or harness is unchanged", () => {
  assertUnchanged(recordedThenEdited(null, "rust", rust("Some(State { next: state.next + 1, ..state })", "Some(State { next: state.next + 2, ..state })")), "rust");
  const commented = rust("kani::assume(invariant(window, state));", '// kani::assume(false);\n        let _text = "kani::assume(false)";\n        kani::assume(invariant(window, state));');
  assertUnchanged(recordedThenEdited(null, "rust", commented), "rust");
});

test("an added Kani stub is changed", () => {
  const outcome = recordedThenEdited(null, "rust", rust("    #[kani::proof]\n    #[kani::unwind(2)]\n    fn claim_keeps_invariant", "    #[kani::proof]\n    #[kani::stub(consume, claim)]\n    #[kani::unwind(2)]\n    fn claim_keeps_invariant"));
  assertChanged(outcome, "rust", "added stub consume, claim");
});

test("an added kani::any_where narrows like an assume and is changed", () => {
  const outcome = recordedThenEdited(null, "rust", rust("let window: u16 = kani::any();", "let window: u16 = kani::any_where(|w: &u16| *w == 1);"));
  assertChanged(outcome, "rust", "added assume |w: &u16| *w == 1");
});

test("a harness and stub written under cfg_attr(kani, ...) are recorded", () => {
  const wrapped = rust("    #[kani::proof]\n    #[kani::unwind(2)]\n    fn claim_keeps_invariant", "    #[cfg_attr(kani, kani::proof)]\n    #[kani::unwind(2)]\n    fn claim_keeps_invariant");
  const removed = recordedThenEdited(wrapped, "rust", rust("    #[cfg_attr(kani, kani::proof)]\n", ""));
  assertChanged(removed, "rust", "removed harness proofs::claim_keeps_invariant");
  const stubbed = recordedThenEdited(null, "rust", rust("    #[kani::proof]\n    #[kani::unwind(2)]\n    fn claim_keeps_invariant", "    #[kani::proof]\n    #[cfg_attr(kani, kani::stub(consume, claim))]\n    #[kani::unwind(2)]\n    fn claim_keeps_invariant"));
  assertChanged(stubbed, "rust", "added stub consume, claim");
});

test("an any_where with a nested turbofish is read as an assume", () => {
  const outcome = recordedThenEdited(null, "rust", rust("let window: u16 = kani::any();", "let window: u16 = kani::any_where::<Option<u16>>(|w| w.is_some()).unwrap();"));
  assertChanged(outcome, "rust", "added assume |w| w.is_some()");
});

test("a Kani path under another crate and a precise capture record", () => {
  const files = models();
  edit(files.rust, "#[cfg(kani)]", "use crate::kani::helpers::proof_state;\nfn keep<'a>(x: &'a u8) -> impl Sized + use<'a> { x }\n#[cfg(kani)]");
  assert.equal(baseline(files.dir, "record", files.record, files.rust).status, 0);
});

test("a Kani form or import the record cannot read fails the record instead of passing unrecorded", () => {
  const forms = [
    ["#[cfg(kani)]", "use kani::assume;\n#[cfg(kani)]", "use kani::assume"],
    ["#[cfg(kani)]", "use ::kani::{any, assume as given};\n#[cfg(kani)]", "use ::kani::{any, assume"],
    ["#[cfg(kani)]", "extern crate kani as k;\n#[cfg(kani)]", "extern crate kani as"],
    ["#[cfg(kani)]", "use {kani as k};\n#[cfg(kani)]", "use {kani as"],
    ["    #[kani::unwind(2)]\n    fn claim_keeps_invariant", "    #[cfg_attr(all(kani, test), kani::stub(consume, claim))]\n    #[kani::unwind(2)]\n    fn claim_keeps_invariant", "kani::stub"],
  ];
  for (const [from, to, named] of forms) {
    const files = models();
    edit(files.rust, from, to);
    const result = baseline(files.dir, "record", files.record, files.rust);
    assert.equal(result.status, 1, to);
    assert.ok(lines(result)[0].startsWith("FAIL baseline:"), result.stdout);
    assert.ok(result.stdout.includes(named), result.stdout);
  }
});

test("re-recording a changed file prints the previous digest, and compare then passes", () => {
  const files = models();
  const first = baseline(files.dir, "record", files.record, files.rust);
  const digest = lines(first)[0].split(" ").at(-1);
  edit(files.rust, "kani::assume(window > 0 && window <= 2);", "kani::assume(window > 0 && window <= 1);");
  const second = lines(baseline(files.dir, "record", files.record, files.rust));
  assert.ok(second[0].startsWith(`RECORDED ${files.rust} `));
  assert.equal(second[1], `  previous ${digest}`);
  assert.equal(baseline(files.dir, "compare", files.record).status, 0);
});

test("recording one file keeps the other entries, and a repeat record prints no previous digest", () => {
  const files = models();
  baseline(files.dir, "record", files.record, files.rust);
  const again = baseline(files.dir, "record", files.record, files.rust);
  assert.equal(lines(again).length, 1);
  baseline(files.dir, "record", files.record, files.matrix, files.statements);
  const result = baseline(files.dir, "compare", files.record);
  assert.equal(result.status, 0);
  assert.equal(lines(result).at(-1), "SUMMARY 3 unchanged, 0 changed");
});

test("a deleted model file is changed", () => {
  assertChanged(recordedThenEdited(null, "rust", ({ rust: path }) => rmSync(path)), "rust", "file is missing");
});

// A harness that an earlier run wrote at the root of a crate of its own, and the production file it
// moves into, where the same functions sit in `mod proofs`. A cover message holds " in ", and
// `inputs` repeats an assumption, so the record has a numbered duplicate.
const harnessBody = [
  "fn inputs() -> u8 { let n: u8 = kani::any(); kani::assume(n < 10); kani::assume(n < 10); n }",
  '#[kani::proof] #[kani::unwind(2)] fn first() { let n = inputs(); kani::cover!(n == 9, "n in range"); }',
  '#[kani::proof] #[kani::unwind(2)] fn second() { let n = inputs(); kani::cover!(n == 0, "n in range"); }',
].join("\n");
const production = "pub fn target(n: u8) -> u8 { n }\n";

function moved(change = (body) => body, module = ["--module", "crate", "proofs"]) {
  const files = models();
  const old = join(files.dir, "verify/lib.rs");
  mkdirSync(join(files.dir, "verify"));
  writeFileSync(old, `use prod::*;\n${harnessBody}\n`);
  assert.equal(baseline(files.dir, "record", files.record, old).status, 0);
  writeFileSync(files.rust, `${production}#[cfg(kani)]\nmod proofs {\n    use super::*;\n${change(harnessBody)}\n}\n`);
  rmSync(old);
  const move = baseline(files.dir, "move", files.record, old, files.rust, ...module);
  return { old, move, ...compared(files) };
}

function compared(files) {
  const result = baseline(files.dir, "compare", files.record);
  return { files, result, out: lines(result) };
}

test("a Kani harness moved into a module of its production file compares unchanged against its old record", () => {
  const outcome = moved();
  assert.equal(outcome.move.status, 0, outcome.move.stdout);
  assert.deepEqual(lines(outcome.move), [`MOVED ${outcome.old} -> ${outcome.files.rust}`]);
  assertUnchanged(outcome, "rust");
});

test("a moved Kani harness that gains an assumption or loses a harness is changed", () => {
  const narrowed = moved((body) => body.replace("let n = inputs();", "let n = inputs(); kani::assume(n == 9);"));
  assertChanged(narrowed, "rust", "added assume n == 9 in proofs::first");
  const dropped = moved((body) => body.split("\n").filter((line) => !line.includes("fn second")).join("\n"));
  assertChanged(dropped, "rust", "removed harness proofs::second", 'removed cover n == 0, "n in range" in proofs::second');
});

test("a move without --module keeps each recorded qualified name", () => {
  const files = models();
  const old = join(files.dir, "verify/lib.rs");
  mkdirSync(join(files.dir, "verify"));
  copyFileSync(files.rust, old);
  assert.equal(baseline(files.dir, "record", files.record, old).status, 0);
  rmSync(old);
  assert.equal(baseline(files.dir, "move", files.record, old, files.rust).status, 0);
  assertUnchanged(compared(files), "rust");
});

test("a move into a recorded production file compares both harness modules", () => {
  const files = models();
  const old = join(files.dir, "verify/lib.rs");
  mkdirSync(join(files.dir, "verify"));
  writeFileSync(old, `use prod::*;\n${harnessBody}\n`);
  const existing = "#[cfg(kani)]\nmod existing {\n    #[kani::proof] #[kani::unwind(2)] fn third() { kani::assume(true); kani::cover!(true); }\n}\n";
  writeFileSync(files.rust, production + existing);
  assert.equal(baseline(files.dir, "record", files.record, old, files.rust).status, 0);
  writeFileSync(files.rust, `${production}${existing}#[cfg(kani)]\nmod proofs {\n    use super::*;\n${harnessBody}\n}\n`);
  rmSync(old);
  assert.equal(baseline(files.dir, "move", files.record, old, files.rust, "--module", "crate", "proofs").status, 0);
  assertUnchanged(compared(files), "rust");
  edit(files.rust, "kani::assume(true);", "");
  assertChanged(compared(files), "rust", "removed assume true in existing::third");
});

test("a move of an unrecorded file or into another kind of model is a usage error", () => {
  const unrecorded = moved();
  const again = baseline(unrecorded.files.dir, "move", unrecorded.files.record, unrecorded.old, unrecorded.files.rust);
  assert.equal(again.status, 2);
  assert.ok(again.stdout.includes("has no record entry"), again.stdout);
  const kind = baseline(unrecorded.files.dir, "move", unrecorded.files.record, unrecorded.files.rust, unrecorded.files.matrix);
  assert.equal(kind.status, 2);
  assert.ok(kind.stdout.includes("not a kani model file"), kind.stdout);
});

test("a malformed record fails", () => {
  const files = models();
  writeFileSync(files.record, "{}\n");
  const result = baseline(files.dir, "compare", files.record);
  assert.equal(result.status, 1);
  assert.ok(lines(result)[0].startsWith("FAIL baseline:"));
});

test("records without execution context are rejected rather than compared as current records", () => {
  const files = models();
  writeFileSync(files.record, JSON.stringify({ format: 1, models: {} }));
  const result = baseline(files.dir, "compare", files.record);
  assert.equal(result.status, 1);
  assert.ok(result.stdout.includes("unsupported record format"));
});

test("an unknown extension and a missing record file are usage errors", () => {
  const files = models();
  writeFileSync(join(files.dir, "notes.txt"), "text\n");
  const unknown = baseline(files.dir, "record", files.record, join(files.dir, "notes.txt"));
  assert.equal(unknown.status, 2);
  assert.ok(unknown.stdout.includes("notes.txt"));
  const missing = baseline(files.dir, "compare", files.record);
  assert.equal(missing.status, 2);
  assert.ok(missing.stdout.includes("does not exist"));
  assert.equal(baseline(files.dir, "frobnicate").status, 2);
});
