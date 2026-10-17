# Rebuilding the selected Lean roots

## Verified result

On 2026-10-16, all **3,177 shipped local modules** were compiled again from their exact pre-comment-revision source bytes into a new, initially empty local-object directory. Neither historical local object directories nor their `LEAN_PATH` entries were used. Both final roots compiled, and all three reports in `RebuildCheck.lean` contained exactly `propext`, `Classical.choice`, and `Quot.sound`.

This is a clean rebuild of the selected **local sources**, using an existing Lean 4.34.1 toolchain and pinned upstream compiled caches. Six absent Mathlib modules were also compiled from their hash-checked pinned sources. It is **not** a clean rebuild of Lean itself or of every upstream dependency. No shipped mathematical source was changed.

The portable `rebuild_selected.py` entry point was checked in two ways: a fresh-output smoke run actually compiled the six missing upstream modules and a local module; its resume/verification path then checked all 3,177 fresh local objects and repeated all three final axiom checks. Full-project compilation used the same Lean command/options in a dependency-ordered runner with resource-aware scheduling. The portable entry point defaults to one compiler process for predictable memory use.

`lake update` was independently tested in a new package-layout view: all nine dependencies resolved to their exact relative `vendor/` paths. `lake env lean RebuildCheck.lean` also passed when connected to the newly compiled objects and the pinned dependency-cache view. A separate, full `lake build` invocation was not used to produce the 3,177 objects.

## Prerequisites

- Python 3.12 or later.
- Lean `leanprover/lean4:v4.34.1`, commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- The nine dependency source directories named in `dependencies.lock.json`.
- Compiled upstream caches for those exact revisions, including ProofWidgets' generated resources. The validation reused these caches; downloading/rebuilding the entire upstream environment was not retested.
- About 10 GiB RAM for the resource settings used here. The script gives its single Lean process a 7,168 MiB limit. Some finite matrix certificates exceeded a 6 GiB limit; smaller limits can produce misleading `decide` reduction diagnostics. The completed local objects occupied about 1.6 GiB, in addition to the toolchain and upstream caches.

## Commands from this `lean/` directory

Verify the shipped source files:

```sh
python3 verify_sources.py
```

If `vendor/` has not been prepared, fetch and hash-check the pinned public source archives:

```sh
python3 prepare_dependencies.py
```

This source-preparation command does not fetch compiled caches or run npm. For a fresh machine, first prepare the pinned upstream cache environment using the upstream Mathlib/Lake procedures. The standard Mathlib cache entry point is `lake exe cache get`; the dependency-resolution step below was tested, but the cache-download/bootstrap step was not repeated in this validation. Do not substitute a different Mathlib revision. If ProofWidgets resources must be built instead of restored from a cache, review its pinned `widget/package.json`, lockfile and Lake build instructions before running its npm workflow.

Resolve the local pinned packages, without an automatic Mathlib cache download during update:

```sh
unset LEAN_PATH
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
```

Run the verified selected-source build entry point:

```sh
python3 rebuild_selected.py --lean "$(command -v lean)" --work-dir .rebuild
```

By default, dependencies are read from `vendor/`. To reuse an already prepared directory containing the nine exact pinned package directories, add `--dependencies /path/to/prepared-dependencies`. Existing cache files are exposed through an output-local symlink view; the build does not overwrite the dependency caches. Missing selected upstream modules are compiled from their matching pinned source hashes.

Resume only this run's successful, hash-verified outputs after an interruption:

```sh
python3 rebuild_selected.py --lean "$(command -v lean)" --work-dir .rebuild --resume
```

Recheck every recorded output hash and repeat the final axiom reports without rebuilding:

```sh
python3 rebuild_selected.py --lean "$(command -v lean)" --work-dir .rebuild --resume --verify-only
```

Use the same `--dependencies` value on resume if it was supplied initially. A fresh build refuses a nonempty output directory. A resume refuses an unrecorded or changed object. Source-hash mismatches, nonzero compiler exits, and unexpected final axiom sets are failures, not permission to replace a proof with `sorry` or add an axiom.

The final reports are `.rebuild/axioms.txt` and `.rebuild/rebuild-summary.json`. Detailed local execution logs and build objects are not part of the source release. `REBUILD_VALIDATION.json` records the concise published acceptance result.

## Mathematical scope

Acceptance covers the selected physical fermion uniform operator-gap root and physical boson full-Fock one-third form/resolvent root. It does not establish every statement in the paper, the separate half-filling zero-mode dimension results, thermodynamic corollaries, an additional fermion full-Fock/spectral wrapper, or the stronger boson asymptotic constant. See `README.md` for the retained scope and provenance qualifications.

## v4 comment revision

After the successful complete local rebuild, obsolete validation-status comments in 35 modules were updated. All 3,177 modules have exactly identical non-comment content to the rebuilt sources; nested comments, quoted strings, character literals and quoted identifiers were handled by the comparison. No second complete compilation was run after this documentation-only revision. `source-manifest.json` records the current bytes; `REBUILD_VALIDATION.json` retains the original build manifest hash and links [COMMENT_ONLY_VALIDATION.json](COMMENT_ONLY_VALIDATION.json). Mathematical and paper-coverage boundaries above are unchanged.

The three additional corrected modules (`RawCARNorm`, `FermionLocalJetFourCouplingDegreeOneLadderBridge01`, and `FermionLocalJetFourCouplingIntegerSourceReflection01`) were also recompiled after their comment edits, each with exit code zero. This supplementary check reused historical dependency objects; see [COMMENT_REVISION_SPOTCHECK.json](COMMENT_REVISION_SPOTCHECK.json). Mathematical uses of “candidate” and source-only evaluation techniques were retained.
