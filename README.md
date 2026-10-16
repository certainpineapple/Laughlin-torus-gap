# Laughlin gaps on large flat tori

Candidate proof for independent review, revised 16 October 2026 from the mathematical draft of 12 October 2026.

prepared by Xiang-Jian Hou with advice from Ying-Hai Wu

**AI contribution and recorded models.** AI agents made substantive contributions to mathematical proof development, Lean formalization, finite certificates and verification code, and manuscript drafting and revision. Their contribution was not limited to language editing. OpenAI Codex was the tool and working environment, not a model name.

The reliably recorded exact model roles are **`gpt-6.1-sol`** and **`gpt-6-astra`**, each performing a separate physical-fidelity review of the actual exported AST for the selected fermionic Lean endpoint. These are internal AI reviews, not independent human peer review. The exact model identifiers for other historical proof-development, formalization, verification-code, and writing tasks were not fully recorded; those tasks are not attributed here to the two recorded review models. See [AI_CONTRIBUTIONS.md](AI_CONTRIBUTIONS.md) for the detailed contribution statement.

The manuscript treats the full lowest-Landau-level bosonic V0 interaction at filling 1/2 and fermionic V1 interaction at filling 1/3. The normalization sets the nonzero planar two-particle energy to one. The geometric hypothesis concerns the actual shortest nonzero lattice vector in units of sqrt(2) times the magnetic length. It does not cover arbitrary thin-torus degenerations.

The mathematical claims and the selected machine acceptance have different scopes. Read [VERIFICATION.md](VERIFICATION.md) and [AI_CONTRIBUTIONS.md](AI_CONTRIBUTIONS.md) before interpreting the formal evidence.

## Contents

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

Two selected exported proof artifacts have recorded kernel acceptance. Clean standalone source reconstruction and provenance reconciliation remain incomplete. This manuscript release contains no Lean source and cannot be used to reproduce that acceptance locally; complete source reproducibility is not claimed.
