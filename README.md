# Laughlin gaps on large flat tori

Candidate proof for independent review, revised 16 October 2026 from the mathematical draft of 12 October 2026.

prepared by Xiang-Jian Hou with advice from Ying-Hai Wu

**AI contribution and recorded models.** AI agents made substantive contributions to mathematical proof development, Lean formalization, finite certificates and verification code, and manuscript drafting and revision. Their contribution was not limited to language editing. OpenAI Codex was the tool and working environment, not a model name.

The reliably recorded exact model roles are **`gpt-6.1-sol`** and **`gpt-6-astra`**, each performing a separate physical-fidelity review of the actual exported AST for both selected fermionic and bosonic Lean endpoints. These are internal AI reviews, not independent human peer review. The exact model identifiers for other historical proof-development, formalization, verification-code, and writing tasks were not fully recorded; those tasks are not attributed here to the two recorded review models. See [AI_CONTRIBUTIONS.md](AI_CONTRIBUTIONS.md) for the detailed contribution statement.

The manuscript treats the full lowest-Landau-level bosonic V0 interaction at filling 1/2 and fermionic V1 interaction at filling 1/3. The normalization sets the nonzero planar two-particle energy to one. The geometric hypothesis concerns the actual shortest nonzero lattice vector in units of sqrt(2) times the magnetic length. It does not cover arbitrary thin-torus degenerations.

The mathematical claims and the selected machine acceptance have different scopes. Read [VERIFICATION.md](VERIFICATION.md) and [AI_CONTRIBUTIONS.md](AI_CONTRIBUTIONS.md) before interpreting the formal evidence.

## Contents

- [lean/](lean/): 3,177 selected local Lean source files, source manifests, dependency pins, licenses, and rebuild instructions. All 3,177 selected local modules were freshly rebuilt with the pinned toolchain and upstream compiled caches; see the precise validation scope below.
- `paper/paper-en.tex` and `paper/paper-zh.tex`: language entrypoints sharing the mathematical body, bibliography, and constants.
- `paper/data/`: seven fermionic rows and 138 bosonic rows, with the retained bosonic finite-certificate results.
- `scripts/`: portable exact rational reconstructions and a PDF build command.
- `output/pdf/`: compiled English and Chinese editions.
- `output/checks/`: newly reproduced finite arithmetic results, when the scripts are run.
- [CITATIONS.md](CITATIONS.md): source identities, method attribution, and the scope of the bibliographic checks.

## Build the manuscript

Install XeLaTeX and BibTeX and provide either TeX Gyre fonts or the Windows fallback fonts selected in `paper/preamble.tex`. The Chinese edition uses Noto CJK fonts or SimSun/Microsoft YaHei. From this directory run:

```text
python scripts/build_paper.py en
python scripts/build_paper.py zh
```

The script uses XeLaTeX directly, then BibTeX and two reference-resolution passes. It does not require Perl or latexmk. Build intermediates remain in the ignored `build/` directory. PDFs go to `output/pdf/`.

## Reconstruct the finite arithmetic

Python 3 and the standard library suffice:

```text
python scripts/verify_boson_planar.py
python scripts/verify_fermion_fourbody.py
python scripts/verify_fermion_scalars.py
```

These are finite coefficient and scalar checks. They do not independently verify the infinite analytic bridges or constitute human peer review.

Two selected exported proof artifacts have recorded ordinary Lean, Nanoda, and empty-Lean replay acceptance. Separate `gpt-6.1-sol` and `gpt-6-astra` reviews of both actual exported ASTs passed. The selected source closure is now included in [lean/](lean/). A fresh rebuild of all 3,177 selected local sources passed without reusing historical local objects, using the pinned toolchain and upstream compiled caches. The v4 release changes comments only: all 3,177 non-comment source streams match the rebuilt sources, and three changed modules were recompiled as supplementary spot checks. The entire closure was not rebuilt again after those comment edits. This is not a full upstream bootstrap, historical source/object provenance reconciliation, or whole-paper formalization. See [lean/REBUILD.md](lean/REBUILD.md) and the machine-readable validation reports.
