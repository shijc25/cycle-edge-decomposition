# Source paths and declaration names

The public Lean source tree uses `Cycle12/`. Some declarations retain the
historical namespace `Cycle13`; namespace names are identifiers, not coefficient
parameters. The final theorem is `Cycle12.coefficient12`, and its statement uses
the integer coefficient 12.

The path migration map is recorded in `release/module-path-map.json`.
The final proof supplies all hypotheses of the intermediate reduction lemmas.
The theorem and its original-edge partition semantics are described in the paper
and checked by `tools/ExactStatement.lean`.
