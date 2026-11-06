# Cycle-edge decompositions with coefficient twelve

**Jiacheng Shi** · Version 1.0.0 · November 6, 2026

This repository accompanies *An explicit bound of twelve for cycle-edge
decompositions*. It contains the paper, the complete Lean proof sources,
quantitative certificates, and verification tools.

For every finite simple graph G, the original edges can be partitioned into
at most **12 (|V(G)| - c(G))** simple cycles and singleton edges, where c(G)
counts all connected components, including isolated vertices.

## Paper and formal theorem

- [Paper PDF](paper/main.pdf) and [LaTeX source](paper/main.tex).
- [Main theorem: Cycle12.coefficient12](Cycle12/Coefficient12Complete.lean).
- [Paper-to-proof correspondence](docs/proof-map.json).
- [Verification record](audit/clean-verification.json).
- [Reproduction guide](docs/REPRODUCING.md).

The proof develops an explicit quantitative refinement of the linear
decomposition framework credited in the paper. It does not claim the first
general linear bound or the first formalization of that bound.

## Verification

The frozen proof closure contains **10,554 Lean modules**. Its recorded build
and main-theorem audit were completed on November 4, 2026 (UTC). The expanded
target checks exact partition of the original edge set and includes isolated
components. The audited dependency closure contains no new axioms and uses only
`propext`, `Classical.choice`, and `Quot.sound`. Generated certificate declarations
are included in the reported declaration counts.

The proof sources in this release are byte-identical to that verified closure.
The release date refers to the manuscript and distribution, not to a new Lean
compilation. The repository records the scope of compilation, cache recovery,
and dependency inspection; it does not claim independent peer review or a
fresh-environment kernel replay.

## Reproduction

Use Python 3.10+, Git, and the Lean version pinned in `lean-toolchain`.
From the repository root:

```sh
python3 scripts/verify_artifact.py --deep-audit
lake exe cache get
python3 scripts/rebuild.py --plan
python3 scripts/rebuild.py --out .cycle12-build --workers 2 --header-cache
python3 scripts/check_target.py --objects .cycle12-build/lib/lean --audit-bodies
```

The first command checks source integrity and recorded evidence without running
Lean. Full recompilation can take many hours. The [reproduction guide](docs/REPRODUCING.md)
explains dependency versions, resource requirements, resumption, and optional
import-header caching. All required proof sources are included; external Lake
packages are obtained at their pinned revisions.

To build the paper:

```sh
cd paper
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

## Source layout

`Cycle12/` contains the proof and certificates; `paper/` contains the manuscript;
`audit/` contains verification evidence; `provenance/` and `LICENSES/` record
third-party sources and licenses. The historical `Cycle13` declaration namespace
is retained for compatibility. Public source paths and the final theorem use
coefficient twelve. Intermediate reduction lemmas state explicit hypotheses;
the final theorem supplies their proofs.

The 83 numerical input chains under `paper/data/` are documentary data. The
paper uses the formally proved constants, with their correspondence recorded
in `paper/data/finite-chain-index.json`.

## Licenses and attribution

Original code and verification scripts are licensed under **Apache-2.0**;
the paper and its LaTeX source are licensed under **CC BY 4.0**. The 52 retained
third-party Lean files preserve their applicable licenses and attribution.
See [LICENSE](LICENSE), [paper/LICENSE.txt](paper/LICENSE.txt), and
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).

AI assistance is disclosed in the final section of the paper. Citation metadata
is provided in [CITATION.cff](CITATION.cff). See [distribution information](docs/PUBLICATION.md)
for the manuscript and software packages.
