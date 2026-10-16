# Verification scope

Acceptance snapshot supplied for editorial use: 16 October 2026, 08:49 UTC. The manuscript revision does not rerun or modify Lean developments.

| Selected endpoint | Accepted mathematical scope |
| --- | --- |
| Fermionic `FermionPhysicalUniformGap` | Original physical H on every particle-number sector. For each positive gamma below 4616733319001/10^14, one finite systole threshold precedes all permitted geometry, common-twist, and particle-number quantifiers. The sector quadratic-form bound is H squared at least gamma H. This endpoint is not an explicit full-Fock spectral wrapper. |
| Bosonic `BosonPhysicalFockThird` | Original unbounded physical H on the full Fock Hilbert sum, systole at least 20, with the 1/3 form bound on D(H). For 0 < lambda < 1/3, a bounded two-sided resolvent has norm at most 1/min(lambda, 1/3-lambda), with the stated domain/range identities. No particle-number cutoff. |

The Geometry, Twist, and physical-carrier hypotheses encoded in the selected definitions remain essential. These endpoints are not statements about an arbitrary abstract two-dimensional Hamiltonian.

Both endpoints have recorded ordinary Lean success, Nanoda checking, and a standalone Lean kernel replay of the same complete actual exported theorem stream from an empty environment. The permitted axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`. The replay also authenticates 23 trusted Init roots. This evidence does not prove the implementation of either checker or the operating system.

Separate gpt-6.1-sol and gpt-6-astra reviews of the fermionic actual exported AST were complete. Bosonic source/display reviews were complete; its actual-AST extraction and two-model review were still pending at this snapshot. None of these model reviews is human peer review.

## Outside the selected formal acceptance

- Explicit fermionic full-Fock spectral wrapper.
- Bosonic half-filling M = 2N kernel dimension two.
- Complete fermionic M = 3N three-dimensional kernel-exhaustion chain.
- Dedicated thermodynamic corollaries, including compact-shape sequences and the bosonic square-torus N >= 64 specialization.
- The stronger bosonic family gamma < 0.33724904107059384, particularly the interval above 1/3.

The mathematical arguments for these claims remain in the paper. This list states the limits of accepted evidence, not that the statements are false or that relevant source material is absent.

## Source reproduction is a separate obligation

The two selected exported proof artifacts have recorded kernel acceptance. Clean standalone source reconstruction and provenance reconciliation remain incomplete. This manuscript release contains no Lean source and cannot be used to reproduce that acceptance locally. Complete source reproducibility is not claimed.

Recorded baseline dependencies:

| Component | Revision |
| --- | --- |
| Lean | 4.34.1, `5045d0056413266e57c625dcd7c365b10e377c52` |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| openai/math | `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` |
| lean4export | `076e8e57707e813375e8f9da8bf989799ace9680` |
| Nanoda library | recorded version 0.4.19, `0f88b5f382f0f3f08aed4af0dd6c0e48c3fd7a44` |

Existing exporter/comparator harnesses adapt a 4.34.0 declaration to 4.34.1. They must not be called untouched official builds. A later source release must include the exact transitive mappings, required certificate data, dependency revisions, notices/licenses, and a relative-path manifest. None is replaced by an old successful object check.
