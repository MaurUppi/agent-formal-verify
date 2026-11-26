# Formal verification

Mutation checks measure whether a model's existing properties detect a planted change.

## Language

**Matrix execution plan**

The ordered TLC runs for a matrix, with the checks in effect at each run. Each reach check belongs to the first matching run in its own spec section, even when another section names the same spec.

**Model kind**

Which checker a model file is for: Lean (`.statements`), TLA+ (`.matrix`) or Kani (`.rs`). The baseline records, compares and moves each kind by its own rules.

**Original check**

A theorem, example or guard in the unmutated Lean model. A mutation failure can be attributed to it when the same check has the same elaborated statement in the mutant. For an example or guard, that identity includes the particular occurrence in the source.

**Route**

How a crate root reaches a Kani harness file: the chain of out-of-line `mod` declarations and `include!` items from the root to the file, with the cfg guards on each step and the module path it gives the file's items. A crate root that no declaration reaches, and a file in no crate, each have one route: from itself, with no guards.
