# Selected Lean sources for the Laughlin torus gap

This source release contains the selected local sources with updated validation-status comments for the two checked core roots, assembled under their logical Lean module names. It contains 3,177 `.lean` files (20,945,196 bytes), including the selected OAI adaptations and the recovered local certificate sources. It does not include old `.olean` files, historical build state, experimental files outside the two recorded import closures, or private paths.

## What has and has not been checked

The selected physical fermion operator-gap root and physical boson full-Fock resolvent root were each exported and checked with Nanoda and an independent empty Lean replay. Their transitive proof axiom closures contain only `propext`, `Classical.choice`, and `Quot.sound`, with no `sorryAx`.

Every shipped local source was checked against its selected SHA-256 and its recorded import header. A conservative lexical scan of all 3,177 shipped local modules, excluding nested comments and quoted strings, found no `sorry`, `admit`, `sorryAx`, or `axiom` token. This source scan is distinct from the kernel result and does not by itself prove that a fresh source build succeeds. On 2026-10-16, **all 3,177 selected local modules passed a fresh local-source rebuild**, followed by successful compilation of both final roots and all three standard-axiom reports. This reused the fixed Lean toolchain and pinned upstream compiled caches, and rebuilt six absent Mathlib modules; it was not a clean rebuild of the entire upstream environment. No mathematical source was changed. The tested portable entry point, dependency-cache requirements, resource guidance and exact acceptance boundary are documented in `REBUILD.md` and `REBUILD_VALIDATION.json`.

The checked roots cover:

* Fermions: the original physical Hamiltonian, all particle-number sectors and twists, with a geometry threshold uniform in particle number for every gamma strictly below 0.04616733319001.
* Bosons: the original physical Hamiltonian on its actual operator domain and full infinite Fock direct sum; systole at least 20 gives the one-third form bound and a bounded two-sided resolvent for each lambda strictly between zero and one third.

This does not establish all statements in the paper. The explicit fermion full-Fock/spectral wrapper, separately accepted half-filling zero-mode dimension results, thermodynamic corollaries, and the stronger boson asymptotic constant remain outside the selected-root acceptance scope. Historical source/object provenance also remains incomplete: the fermion record has 180 unjoined historical project-source events and 1,779 unresolved official compiled-artifact origins; a fixed list of 32 legacy libraries has identity-only provenance. The boson historical provenance record is likewise incomplete. These limitations do not erase the actual checks on the exported core proofs and are not a percentage measure of mathematical correctness.

## Rebuild prerequisites and commands

Use a new output directory, Lean `leanprover/lean4:v4.34.1`, and the exact dependencies in `dependencies.lock.json`. The executable entry point is `rebuild_selected.py`; see **[REBUILD.md](REBUILD.md)** for the tested commands, cache prerequisites, safe resume and final axiom checks.

`lake update` was tested in a fresh package-layout view and resolved all nine dependencies to the pinned local paths. `lake env lean RebuildCheck.lean` passed using the newly compiled local objects. The complete local-source rebuild was driven by explicit Lean commands in dependency order, not a separately validated full `lake build` invocation.

OAI is already vendored in `Lean/OAI`; its upstream Lake package and patch hooks are not loaded. Hash or compilation failures must be reported, not bypassed by changing a theorem or dependency revision.

## Files and attribution

`source-manifest.json` gives each local logical path, module, profile, byte count, SHA-256 and imports. `SOURCE_SCAN.json` records the lexical scan scope. `LICENSES/` preserves upstream dependency and OAI license texts. Existing copyright notices remain in the sources. No new blanket license for the original project is inferred or granted by this release.

OAI files are selected local adaptations/recoveries based on `openai/math` revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, not a claim that every file is an unchanged upstream copy. In particular the selected `Model` uses narrowed imports. This release preserves the selected mathematical content without editing proofs.

## Comment-only revision (v4)

The full 3,177-module rebuild and final axiom checks were completed on the pre-revision source bytes. This revision updates obsolete drafting-status comments in 35 modules. Every module was compared against v2 with nested Lean comments removed and strings preserved: all non-comment contents, including whitespace, are identical. No proof statement, proof body, import or option changed. See [COMMENT_ONLY_VALIDATION.json](COMMENT_ONLY_VALIDATION.json). This is post-build comment equivalence verification, not a second full compilation or an expansion of the accepted paper scope. The source manifest now records the revised bytes.

The three additional corrected modules (`RawCARNorm`, `FermionLocalJetFourCouplingDegreeOneLadderBridge01`, and `FermionLocalJetFourCouplingIntegerSourceReflection01`) were also recompiled after their comment edits, each with exit code zero. This supplementary check reused historical dependency objects; see [COMMENT_REVISION_SPOTCHECK.json](COMMENT_REVISION_SPOTCHECK.json). Mathematical uses of “candidate” and source-only evaluation techniques were retained.
