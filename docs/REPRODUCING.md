# Reproducing the coefficient-12 proof

## Fixed inputs

- Lean 4.34.1, pinned in `lean-toolchain`.
- Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
- Transitive Lake revisions in `lake-manifest.json`.
- Python 3.10+ and Git; TeX/latexmk only for the paper.

Run from the repository root. `lake exe cache get` obtains the fixed external cache.
Do not run `lake update` to change revisions. All 10,554 required project modules are
included. The removed ErdosProblems and ProbMethodCombinatorics libraries are not needed.

## Three checks

1. `python3 scripts/verify_artifact.py --deep-audit` checks current source hashes,
   successful compilation records, the compressed body-audit digest, the allowed axioms,
   absence of removed libraries and the paper's declaration map. It does not run Lean
   and refuses an unverified candidate.
2. `python3 scripts/rebuild.py --out .cycle12-build --workers 2 --header-cache` compiles
   the closure. Its project search path contains only that output. Nonempty output requires
   `--resume`, which validates source hashes, dependency revisions, dependency completion,
   and journaled object hashes, including associated server/private objects when present.
3. `python3 scripts/check_target.py --objects .cycle12-build/lib/lean --audit-bodies`
   compiles the expanded exact edge-partition statement, checks printed axioms, and traverses
   actual types and values from the main theorem. It rejects missing bodies, project axioms,
   unsafe/partial dependencies and the removed libraries.

Omit `--header-cache` for ordinary compilation throughout. Snapshots, when enabled, contain
imports only and are built from current objects. An ordinary/cached probe must produce
identical object hashes before reuse. Every source body is still compiled. Snapshots are
removed when their group completes; evidence is retained.
The evidence covers each snapshot generation used in the journal. Probe records lost at
a restart or storage reset require a new ordinary compilation matching the actual earlier
cached object byte for byte. These retrospective comparisons are distinguished from original
probe records in `audit/import-header-generations.json`; the earlier bank comparison is also
recorded in `audit/previous-header-replay.json`.

`--plan` checks inventory and import order without compilation. `--target MODULE` selects
a diagnostic closure, not a complete main-theorem build. The default has no per-module timeout;
`--timeout SECONDS` is optional. Resume an interrupted build by adding `--resume`. Old
failures remain journaled and require a later successful record for the same frozen source.

Build/check scripts accept explicit `--lean` and `--packages` paths. They reject changed
tracked external sources and mismatched revisions. No C build is needed. With 16 GiB RAM,
start with two workers or use one for the largest modules. Allow several gigabytes and many hours.

On Linux with cgroup memory accounting, `--workers 2 --certificate-workers 4` optionally
allows up to four selected small certificate modules to run together. Other modules retain
the two-worker limit. Extra dispatch requires at least 1 GiB of memory headroom and limits
the combined anonymous and shared-memory footprint; when accounting is unavailable, the
ordinary worker limit applies. This changes scheduling only. The recorded resource probes
and transition for this build are in `audit/build-scheduling-transition.json`.

## Evidence scope

The recorded build recompiles the complete closure after replacement of two libraries. `audit/clean-verification.json` binds
current source hashes, compilation journal, target log and dependency report. Completion
status and current declaration counts are recorded there and in `release/status.json`.

Some objects may be resumed from this same replacement build's development stage, after
checking source, dependency and object hashes. After temporary storage was lost, some object
bytes were recovered from historical caches only because they exactly matched the hashes
of actual compilations already recorded in this replacement run. The optional
`--resume --restore-exact-current-run` recovery mode additionally requires the same recorded
prerequisite object hashes; it does not fabricate a new compilation record. Unmatched objects
are regenerated. `audit/storage-recovery-2026-11-04.json` and the associated recovery records
identify this operation explicitly. Fixed external Lean/Mathlib objects are reused.
The optional empty-environment replay in `tools/InspectMain.lean` is disabled by the wrapper.
No independent peer review is claimed.

The allowed axioms are `propext`, `Classical.choice` and `Quot.sound`. Large declaration
counts include generated certificates and auxiliary declarations. Recorded machine paths
are evidence, not portable configuration. New checks write to `.cycle12-check`.

The manuscript validation script also uses Poppler (`pdfinfo`/`pdftotext`)
for manuscript checks; these tools are not needed for Lean verification.
