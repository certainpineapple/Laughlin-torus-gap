import torus.shared.ThermalCoherentAnchoredMoments
import Mathlib.Analysis.SpecificLimits.Normed

/-! Summable absolute full-plane anchored coefficients with arbitrary fixed
polynomial index budgets. This is a scalar L1 majorant only; physical row
coefficient bounds and their actual kernel identity are separate. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentAnchoredMoments
open MeasureTheory TorusLean.Fermion.PlaneMagneticUnitary

private theorem sqrt_fraction_pos_lt_one (x : ℝ) (hx0 : 0<x) (hx1 : x<1) :
    0<Real.sqrt x ∧ Real.sqrt x<1 := by
  constructor
  · exact Real.sqrt_pos.mpr hx0
  · rw [Real.sqrt_lt hx0.le (by norm_num : (0:ℝ)≤1)]
    simpa using hx1

private theorem polynomial_geometric_summable (k : ℕ) (r : ℝ)
    (hr0 : 0<r) (hr1 : r<1) :
    Summable (fun n : ℕ => ((n:ℝ)+1)^k*r^n) := by
  have hr : ‖r‖<1 := by simpa only [Real.norm_eq_abs,abs_of_pos hr0] using hr1
  have ht := summable_pow_mul_geometric_of_norm_lt_one k hr
  have hu : Summable (fun n : ℕ => (((n+1:ℕ):ℝ)^k*r^(n+1))) :=
    (summable_nat_add_iff 1).mpr ht
  have hv := hu.mul_left r⁻¹
  convert hv using 1
  funext n
  simp only [Nat.cast_add,Nat.cast_one,pow_succ]
  field_simp [ne_of_gt hr0]

/-- Absolute integral norms are doubly summable even after either index is
multiplied by any fixed natural-power budget. No cancellation is used. -/
theorem anchoredPlaneCoefficient_polynomial_integral_norm_summable (p q : ℕ) :
    Summable (fun jl : ℕ×ℕ => ((jl.1:ℝ)+1)^p*((jl.2:ℝ)+1)^q*
      (∫ z, ‖anchoredPlaneCoefficient jl.1 jl.2 z‖ ∂planeMeasure)) := by
  have hj := sqrt_fraction_pos_lt_one (2/3) (by norm_num) (by norm_num)
  have hl := sqrt_fraction_pos_lt_one (4/5) (by norm_num) (by norm_num)
  have hJ := polynomial_geometric_summable p _ hj.1 hj.2
  have hL := polynomial_geometric_summable q _ hl.1 hl.2
  have hm := (hJ.mul_of_nonneg hL (fun n => by positivity) (fun n => by positivity)).mul_left
    (2/Real.sqrt (15:ℝ))
  apply Summable.of_nonneg_of_le
    (fun jl => mul_nonneg (by positivity) (integral_nonneg (fun z => norm_nonneg _)))
    (fun jl => ?_) hm
  have h := mul_le_mul_of_nonneg_left
    (anchoredPlaneCoefficient_integral_norm_le jl.1 jl.2)
    (show 0≤((jl.1:ℝ)+1)^p*((jl.2:ℝ)+1)^q by positivity)
  convert h using 1 <;> ring

theorem anchoredPlaneCoefficient_integral_norm_summable :
    Summable (fun jl : ℕ×ℕ => ∫ z, ‖anchoredPlaneCoefficient jl.1 jl.2 z‖ ∂planeMeasure) := by
  simpa only [pow_zero,one_mul] using
    anchoredPlaneCoefficient_polynomial_integral_norm_summable 0 0

end TorusLean.Shared.ThermalCoherentAnchoredMoments
