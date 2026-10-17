import torus.fermion.RawPairCAR
import OAI.Analysis.Laughlin.Operators.WeightedOccupationNorm
import PaperPauliCoefficients
import Mathlib.Tactic.Linarith

/-! Rebuilt successfully with Lean 4.34.1 in the selected 3,177-module closure.
See [validation scope](../REBUILD.md) and ../REBUILD_VALIDATION.json.
Exact CAR norm identity on the existing official coordinate Fock space.
`Orbital Q`'s default Pi norm is not the physical Hilbert norm. The orbital
factor below is explicitly the coordinate square sum. No N-uniform estimate
or physical torus unitary correspondence is assumed. -/

set_option autoImplicit false

namespace TorusLean.Fermion

open OAI.Laughlin.Fock
open scoped BigOperators

theorem rawGram_self_eq_coordinateNormSq (Q : ℕ) (v : Orbital Q) :
    rawGram Q v v = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
  rw [rawGram_eq_sum, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rfl

theorem rawCreate_adjoint_right (Q : ℕ) (v : Orbital Q) (x y : Space Q) :
    occupationInner Q x (rawCreate Q v y) =
      occupationInner Q (vectorAnnihilate Q v x) y := by
  have h := congrArg star (rawCreate_adjoint Q v y x)
  simpa only [occupationInner_star] using h

theorem raw_CAR_normSq_identity (Q : ℕ) (v : Orbital Q) (x : Space Q) :
    occupationNormSq Q (vectorAnnihilate Q v x) +
        occupationNormSq Q (rawCreate Q v x) =
      (∑ i, ‖v i‖ ^ 2) * occupationNormSq Q x := by
  have hcar := LinearMap.congr_fun (raw_annihilate_create Q v v) x
  simp only [Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    Module.End.one_apply] at hcar
  have hsub : ∀ y w : Space Q,
      occupationInner Q x (y - w) = occupationInner Q x y - occupationInner Q x w := by
    intro y w
    simp [occupationInner, mul_sub, Finset.sum_sub_distrib]
  have h : ((occupationNormSq Q (vectorAnnihilate Q v x) : ℝ) : ℂ) +
      (occupationNormSq Q (rawCreate Q v x) : ℂ) =
      ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) * (occupationNormSq Q x : ℂ) := by
    rw [← occupationInner_self, ← occupationInner_self,
      ← rawCreate_adjoint_right, rawCreate_adjoint, hcar, hsub,
      occupationInner_smul_right, rawGram_self_eq_coordinateNormSq,
      occupationInner_self]
    ring
  simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] using congrArg Complex.re h

theorem raw_annihilate_normSq_le (Q : ℕ) (v : Orbital Q) (x : Space Q) :
    occupationNormSq Q (vectorAnnihilate Q v x) ≤
      (∑ i, ‖v i‖ ^ 2) * occupationNormSq Q x := by
  have h := raw_CAR_normSq_identity Q v x
  have hp := occupationNormSq_nonneg Q (rawCreate Q v x)
  linarith

/-- The actual real paper coefficients and actual CAR annihilators. The pair
amplitudes remain arguments until the root-owned physical pair is available.
For eq:F-Pauli-tail, `u p` must be the coordinates of jet `u_{z-p}^T(R)`
and `b p` must be the actual pair amplitude `B_p(R) psi`.
The RHS keeps the actual coordinate Gram norms; no jet envelope is assumed. -/
theorem paperPauli_local_coordinate_bound (Q z : ℕ)
    (u : Fin (z + 1) → Orbital Q) (b : Fin (z + 1) → Space Q) :
    occupationNormSq Q
        (∑ p : Fin (z + 1), (paperPauliCoefficient z p.val : ℂ) •
          vectorAnnihilate Q (u p) (b p)) ≤
      ∑ p : Fin (z + 1), (∑ i, ‖u p i‖ ^ 2) * occupationNormSq Q (b p) := by
  apply (normalized_occupation_sum_bound Q
    (fun p : Fin (z + 1) => paperPauliCoefficient z p.val)
    (fun p => vectorAnnihilate Q (u p) (b p))
    (paperPauliCoefficient_sq_sum z)).trans
  exact Finset.sum_le_sum (fun p hp => raw_annihilate_normSq_le Q (u p) (b p))

end TorusLean.Fermion
