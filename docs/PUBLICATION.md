# Distribution and citation

Version 1.0.0 is dated November 6, 2026. Author: Jiacheng Shi.

The distribution provides three files:

| File | Contents | License |
| --- | --- | --- |
| `cycle12-paper.pdf` | The research paper | CC BY 4.0 |
| `cycle12-paper-source.zip` | LaTeX source and paper data | CC BY 4.0 |
| `cycle12-complete-source.zip` | Paper, Lean sources, certificates and verification tools | Apache-2.0 for original software; CC BY 4.0 for the paper; retained third-party licenses apply |

The complete archive contains every required local Lean module. External Lake
packages are obtained at the revisions pinned in `lake-manifest.json`.
Verification scope and reproduction instructions are in `docs/REPRODUCING.md`.
The original source, object and theorem-audit records retain their verification
dates. The distribution date does not imply that Lean was recompiled on that date.

`CITATION.cff` supplies citation metadata. `.zenodo.json` describes the software
artifact; `release/zenodo-paper.json` describes the preprint. These are separate
resource types with separate licenses. DOI identifiers belong to the corresponding
published records and are not assigned by the local build scripts.

To generate a checked complete source archive:

```sh
python3 scripts/export_public.py --output /path/to/cycle12-complete-source.zip
```

The exporter checks the frozen proof sources, recorded audit evidence, manuscript
inputs, final file inventory, archive CRCs and per-file SHA256 digests.
