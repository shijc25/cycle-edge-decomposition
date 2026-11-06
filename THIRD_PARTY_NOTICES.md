# Third-party notices

The project-owned Lean sources and verification scripts are released under Apache-2.0.
The manuscript is separately licensed CC BY 4.0. Third-party notices and license texts
retain their original scope.

The current source package includes 52 unmodified Lean files from the following projects.
Their pinned revisions, file hashes, and license evidence are recorded in
`provenance/retained-sources.json` and `provenance/license-review.json`.

| Dependency | Pinned revision | License |
| --- | --- | --- |
| [berge-matching](https://github.com/jtraverso/berge-matching) | `f01d042c071c778fb3f432312356136a92369076` | Apache-2.0 |
| [euler-petersen](https://github.com/jtraverso/euler-petersen) | `02c3f1a5327c5f066938860bb07e9fce226b36ca` | Apache-2.0 |
| [haggkvist-janssen](https://github.com/jtraverso/haggkvist-janssen) | `807e08bd7c480d4fae80c1b78377d23989d39ab0` | Apache-2.0 |
| [haxell](https://github.com/mbucic4/Nearly-spanning-Lovasz) | `7f2728d07ce648ed74cae08bbfa7084b9ec13f4b` | Apache-2.0 |
| [karger](https://github.com/AntoineduFresne/Master-Thesis) | `b964d9ef3d30471841814f0d42ffb391e78ff2a4` | Apache-2.0 |
| [menger](https://github.com/jtraverso/menger-hamiltonian) | `35c5f684f9bfbd244bd0999ce725623ab571adb6` | Apache-2.0 |
| [openai](https://github.com/openai/math) | `1581d4cbdd69a0faf34b2089614fe2a814316a6a` | Apache-2.0 |

Copies of the applicable licenses are in `LICENSES/`. Lean, Mathlib and the other
Lake packages are obtained at the versions fixed in `lean-toolchain` and
`lake-manifest.json`; their distribution retains their own notices. Of the nine
Lake dependencies, Cli has an MIT root license and the other eight have Apache-2.0
root licenses. These package source trees are not bundled in this repository.

The earlier proof imported 26 files from `plby/lean-proofs` and three from
`yidiq7/ProbMethodCombinatorics`. An applicable source grant had not been established
for 23 of those files. Both groups have been removed from the current import closure
and from the public source tree. They are no longer fetched by the reproduction procedure.
The replacement implementations in `Cycle12/Independent/` use mathematical statements,
Mathlib primitives and separately organized proofs: a Woodall rotation/deletion argument
for the precise Erdős–Gallai bound, and finite-product/FKG/Laplace proofs for sampling.
Historical source exposure is recorded; no formal clean-room claim is made.
The classical mathematics and the earlier formal libraries remain credited in the
bibliography and `provenance/replaced-dependencies.json`.

The linear decomposition framework and its retained formal infrastructure are credited
principally to OpenAI’s September 2026 manuscript and formal library. The manuscript
also cites the related graph decomposition, immersion, matching and probability results.
Generated certificate declarations do not change the attribution of those inputs.

The exact retained source blobs and their ancestor license/notice files were also
checked at those pinned revisions. Six complete recursive repository trees and
complete nonrecursive source-ancestor listings for OpenAI were examined. No additional
applicable NOTICE file was found in those locations; the license copies match.
See `provenance/notice-tree-review.json` for the precise scope and hashes.
