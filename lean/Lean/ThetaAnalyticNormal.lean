import ThetaAnalytic
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

/-!
Normal convergence of the full bilateral residue-class Fourier series.
On every compact subset of the complex plane there is one summable real
majorant for all integer-indexed summands. The resulting finite-sum net
converges uniformly to the analytic residue section.

The twists may be arbitrary complex numbers. These statements do not assume
Fourier completeness of arbitrary holomorphic sections or identify a physical
Hamiltonian kernel.
-/

noncomputable section

namespace TorusLean.Geometry.ThetaAnalytic

open Complex Real Filter

theorem continuous_fourierTerm (d : ℕ) (tau sigma psi : ℂ) (n : ℤ) :
    Continuous (fun z : ℂ => fourierTerm d tau sigma psi z n) := by
  unfold fourierTerm
  fun_prop

theorem continuous_thetaArgument (d : ℕ) (tau sigma psi : ℂ) (r : ℤ) :
    Continuous (thetaArgument d tau sigma psi r) := by
  unfold thetaArgument
  fun_prop

/-- The Weierstrass majorant criterion on every compact set, for both integer
tails of one residue-class Fourier series simultaneously. -/
theorem residueTerm_normal_convergence (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (r : ℤ) (K : Set ℂ) (hK : IsCompact K) :
    ∃ b : ℤ → ℝ, Summable b ∧
      ∀ z ∈ K, ∀ k : ℤ, ‖residueTerm d tau sigma psi r z k‖ ≤ b k := by
  obtain ⟨C, hC⟩ := hK.bddAbove_image
    (continuous_fourierTerm d tau sigma psi r).norm.continuousOn
  obtain ⟨S, hS⟩ := hK.bddAbove_image
    (_root_.continuous_abs.comp
      (Complex.continuous_im.comp (continuous_thetaArgument d tau sigma psi r))).continuousOn
  let T : ℝ := ((d : ℂ) * tau).im
  have hT : 0 < T := scaled_tau_im_pos d tau hτ
  have hsum : Summable
      (fun k : ℤ => Real.exp (-π * (T * (k : ℝ) ^ 2 - 2 * S * |(k : ℝ)|))) := by
    simpa only [pow_zero, one_mul, Int.cast_abs] using
      summable_pow_mul_jacobiTheta₂_term_bound S hT 0
  refine ⟨fun k : ℤ => max C 0 *
    Real.exp (-π * (T * (k : ℝ) ^ 2 - 2 * S * |(k : ℝ)|)), hsum.mul_left _, ?_⟩
  intro z hz k
  have hCz : ‖fourierTerm d tau sigma psi z r‖ ≤ max C 0 :=
    (hC ⟨z, hz, rfl⟩).trans (le_max_left C 0)
  have hSz : |(thetaArgument d tau sigma psi r z).im| ≤ S := hS ⟨z, hz, rfl⟩
  have htheta := norm_jacobiTheta₂_term_le hT hSz
    (show T ≤ ((d : ℂ) * tau).im from le_rfl) k
  simp only [Int.cast_abs] at htheta
  rw [residueTerm_eq_thetaTerm, norm_mul]
  exact mul_le_mul hCz htheta (norm_nonneg _) (le_max_right C 0)

/-- All finite integer partial sums converge uniformly on every compact set.
The indexing filter is `atTop` on finite subsets of `ℤ`, so no tail is omitted. -/
theorem residueTerm_tendstoUniformlyOn (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (r : ℤ) (K : Set ℂ) (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun s : Finset ℤ => fun z : ℂ => ∑ k ∈ s, residueTerm d tau sigma psi r z k)
      (residueSection d tau sigma psi r) atTop K := by
  obtain ⟨b, hb, hbound⟩ := residueTerm_normal_convergence d tau sigma psi hτ r K hK
  have h := tendstoUniformlyOn_tsum
    (f := fun k z => residueTerm d tau sigma psi r z k) hb (fun k z hz => hbound z hz k)
  simpa only [residueTerm_tsum d tau sigma psi hτ r] using h

end TorusLean.Geometry.ThetaAnalytic
