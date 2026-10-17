import torus.shared.BosonPairCOMCoefficientBound
import torus.shared.NatAnchoredThreeAction

/-! Exact generating-series rescaling of the unchanged ordered pair-COM
coefficient. This is a scalar identity, not a spectral-series assumption. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonPairCOMGeneratingCoefficient
open TorusLean.BosonFiniteCertificate
open TorusLean.Shared.BosonPairCOMCoefficientBound

theorem pairCOMCoefficientReal_generating (l i : ℕ) (hi : i ≤ l) :
    ((Real.sqrt (2:ℝ))^l / Real.sqrt (l.factorial:ℝ)) * pairCOMCoefficientReal l i =
      (1 / Real.sqrt (2:ℝ)) /
        (Real.sqrt (i.factorial:ℝ) * Real.sqrt ((l-i).factorial:ℝ)) := by
  have h0 : Real.sqrt (2:ℝ) ≠ 0 := by positivity
  have hl : Real.sqrt (l.factorial:ℝ) ≠ 0 := by positivity
  have hi0 : Real.sqrt (i.factorial:ℝ) ≠ 0 := by positivity
  have hj0 : Real.sqrt ((l-i).factorial:ℝ) ≠ 0 := by positivity
  have hf : (l.choose i : ℝ) * (i.factorial:ℝ) * ((l-i).factorial:ℝ) =
      (l.factorial:ℝ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have hroot : Real.sqrt ((2:ℝ)^l * (l.factorial:ℝ)) =
      (Real.sqrt (2:ℝ))^l * Real.sqrt (l.factorial:ℝ) := by
    rw [Real.sqrt_mul (by positivity), natAnchoredThree_sqrt_pow]
  have hr : (l.choose i : ℝ) * Real.sqrt (i.factorial:ℝ) *
      Real.sqrt ((l-i).factorial:ℝ) =
      (Real.sqrt (l.factorial:ℝ))^2 /
        (Real.sqrt (i.factorial:ℝ) * Real.sqrt ((l-i).factorial:ℝ)) := by
    apply (eq_div_iff (mul_ne_zero hi0 hj0)).mpr
    calc
      _ = (l.choose i : ℝ) * (Real.sqrt (i.factorial:ℝ))^2 *
          (Real.sqrt ((l-i).factorial:ℝ))^2 := by ring
      _ = _ := by
        rw [Real.sq_sqrt (by positivity : (0:ℝ) ≤ i.factorial),
          Real.sq_sqrt (by positivity : (0:ℝ) ≤ (l-i).factorial),
          Real.sq_sqrt (by positivity : (0:ℝ) ≤ l.factorial), hf]
  unfold pairCOMCoefficientReal
  rw [hroot, hr]
  field_simp [h0, hl, hi0, hj0]
  <;> ring

#print axioms pairCOMCoefficientReal_generating
end TorusLean.Shared.BosonPairCOMGeneratingCoefficient
