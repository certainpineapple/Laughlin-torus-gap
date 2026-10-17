# Verification scope

Selected-core acceptance and source-release update: 17 October 2026. The source validation below is distinct from the earlier exported-object checks.

| Selected endpoint | Accepted mathematical scope |
| --- | --- |
| Fermionic `FermionPhysicalUniformGap` | Original physical H on every particle-number sector. For each positive gamma below 4616733319001/10^14, one finite systole threshold precedes all permitted geometry, common-twist, and particle-number quantifiers. The sector quadratic-form bound is H squared at least gamma H. This endpoint is not an explicit full-Fock spectral wrapper. |
| Bosonic `BosonPhysicalFockThird` | Original unbounded physical H on the full Fock Hilbert sum, systole at least 20, with the 1/3 form bound on D(H). For 0 < lambda < 1/3, a bounded two-sided resolvent has norm at most 1/min(lambda, 1/3-lambda), with the stated domain/range identities. No particle-number cutoff. |

The Geometry, Twist, and physical-carrier hypotheses encoded in the selected definitions remain essential. These endpoints are not statements about an arbitrary abstract two-dimensional Hamiltonian.

Both endpoints have recorded ordinary Lean success, Nanoda checking, and a standalone Lean kernel replay of the same complete actual exported theorem stream from an empty environment. The permitted axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`. The replay also authenticates 23 trusted Init roots. This evidence does not prove the implementation of either checker or the operating system.

Separate `gpt-6.1-sol` and `gpt-6-astra` physical-fidelity reviews of the actual exported type/value expressions passed for both the fermionic and bosonic selected endpoints. None of these model reviews is human peer review.

## Outside the selected formal acceptance

- Explicit fermionic full-Fock spectral wrapper.
- Bosonic half-filling M = 2N kernel dimension two.
- Complete fermionic M = 3N three-dimensional kernel-exhaustion chain.
- Dedicated thermodynamic corollaries, including compact-shape sequences and the bosonic square-torus N >= 64 specialization.
- The stronger bosonic family gamma < 0.33724904107059384, particularly the interval above 1/3.

The mathematical arguments for these claims remain in the paper. This list states the limits of accepted evidence, not that the statements are false or that relevant source material is absent.

## Selected local source rebuild and its limits

The selected source closure is included in [lean/](lean/): 3,177 local Lean source files, byte-for-byte selected-source manifest, import mappings, required local certificate sources, nine pinned upstream dependencies, and notices/licenses. An independent package check passed against the public manifest. A conservative lexical scan found no `sorry`, `admit`, `sorryAx`, or `axiom` token in those local modules. This scan is distinct from kernel checking.

A fresh rebuild of all 3,177 selected local modules passed on 16 October 2026 using Lean 4.34.1 and the pinned dependencies. No historical local compiled objects were reused. Upstream compiled caches were reused, with six upstream modules recompiled; this is not a complete source bootstrap of Lean and every dependency. The three selected endpoint declarations reported only `propext`, `Classical.choice`, and `Quot.sound`. Portable-entrypoint fresh smoke and full-output verification, `lake update`, and a final `lake env` axiom check passed; a separate full `lake build` was not reexecuted. See [lean/REBUILD_VALIDATION.json](lean/REBUILD_VALIDATION.json).

After that full local rebuild, 35 modules received comment-only corrections. All 3,177 non-comment source streams were checked for equality against the rebuilt version. Three revised modules were additionally compiled into new outputs with existing historical dependency objects; this was a supplementary spot check, not a second fresh closure rebuild. See [lean/COMMENT_ONLY_VALIDATION.json](lean/COMMENT_ONLY_VALIDATION.json) and [lean/COMMENT_REVISION_SPOTCHECK.json](lean/COMMENT_REVISION_SPOTCHECK.json). Build instructions and these limits are in [lean/REBUILD.md](lean/REBUILD.md).

Historical source/object provenance reconciliation remains separate and incomplete. Successful source rebuilding does not extend the selected theorem scopes to every claim in the paper, and no human peer review or completed whole-paper formalization is claimed.

Recorded baseline dependencies:

| Component | Revision |
| --- | --- |
| Lean | 4.34.1, `5045d0056413266e57c625dcd7c365b10e377c52` |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| openai/math | `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` |
| lean4export | `076e8e57707e813375e8f9da8bf989799ace9680` |
| Nanoda library | recorded version 0.4.19, `0f88b5f382f0f3f08aed4af0dd6c0e48c3fd7a44` |

Existing exporter/comparator harnesses adapt a 4.34.0 declaration to 4.34.1. They must not be called untouched official builds. The present selected source release supplies transitive mappings, required local certificate sources, dependency revisions, notices/licenses, and relative-path manifests. The fresh local rebuild supplies additional source evidence within the explicitly stated cache and comment-revision limits; it does not turn the historical object checks into a full upstream bootstrap.
