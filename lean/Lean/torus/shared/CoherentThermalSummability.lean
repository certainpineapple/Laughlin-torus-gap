import torus.shared.PlaneJetGramBounds
import Mathlib.Analysis.SpecificLimits.Normed

/-! Absolute summability budgets for the genuine torus jets.  These bounds
control the later weighted double series before any exchange with a plane
integral.  No thermal operator identity is assumed. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.CoherentThermalSummability
open TorusLean.Geometry TorusLean.Fermion.LatticePacking
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.PlaneJetGramBounds

def thermalRootRatio (a : ℝ) : ℝ := (Real.sqrt (1+a))⁻¹

theorem thermalRootRatio_pos_lt_one (a : ℝ) (ha : 0 < a) :
    0 < thermalRootRatio a ∧ thermalRootRatio a < 1 := by
  have hs : 1 < Real.sqrt (1+a) := by
    rw [Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 1)]
    nlinarith
  constructor
  · unfold thermalRootRatio
    positivity
  · exact inv_lt_one_of_one_lt₀ hs

theorem sqrt_thermalEigenvalue (a : ℝ) (ha : 0 < a) (j : ℕ) :
    Real.sqrt (((1+a)^(j+1))⁻¹) = thermalRootRatio a ^ (j+1) := by
  have hp (n : ℕ) : Real.sqrt ((1+a)^n) = (Real.sqrt (1+a))^n := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg (by positivity) n), ih, pow_succ]
  rw [Real.sqrt_inv, hp, ← inv_pow]
  rfl

theorem geometric_linear_summable (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (C : ℝ) :
    Summable (fun j : ℕ => r^(j+1) * (C * (1+(j:ℝ))+1)) := by
  have hr : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1
  have h0 := summable_geometric_of_norm_lt_one hr
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h := ((h0.mul_left (r*(C+1))).add (h1.mul_left (r*C)))
  convert h using 1
  ext j
  simp only [pow_succ]
  ring

/-- The physical norm, uniformly in center and twist, has a summable
geometric thermal majorant for every positive Gaussian parameter. -/
theorem weighted_rawPlaneJet_norm_summable (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (a : ℝ) (ha : 0 < a) (R : ℂ) :
    Summable (fun j : ℕ => thermalRootRatio a ^ (j+1) * ‖rawPlaneJet G theta j R‖) := by
  obtain ⟨hr0,hr1⟩ := thermalRootRatio_pos_lt_one a ha
  apply Summable.of_nonneg_of_le (fun j => mul_nonneg (pow_nonneg hr0.le _) (norm_nonneg _))
    (fun j => ?_) (geometric_linear_summable _ hr0.le hr1 (4096+gaussianConstant))
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr0.le _)
  have hb := rawPlaneJet_norm_sq_le G theta hG j R
  nlinarith [sq_nonneg ‖rawPlaneJet G theta j R‖,
    sq_nonneg (‖rawPlaneJet G theta j R‖ - 1)]

/-- Absolute double-series majorant for thermal cross matrix elements.
This is summability in both indices, before using cancellation of moments. -/
theorem weighted_rawPlaneJet_double_summable (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (a : ℝ) (ha : 0 < a) (R : ℂ) :
    Summable (fun jm : ℕ × ℕ =>
      (thermalRootRatio a ^ (jm.1+1) * ‖rawPlaneJet G theta jm.1 R‖) *
      (thermalRootRatio a ^ (jm.2+1) * ‖rawPlaneJet G theta jm.2 R‖)) := by
  have h := weighted_rawPlaneJet_norm_summable G theta hG a ha R
  have hn (j : ℕ) : 0 ≤ thermalRootRatio a ^ (j+1) * ‖rawPlaneJet G theta j R‖ :=
    mul_nonneg (pow_nonneg (thermalRootRatio_pos_lt_one a ha).1.le _) (norm_nonneg _)
  exact h.mul_of_nonneg h hn hn

/-- Actual Hilbert pairing coefficients inherit the same summable thermal
budget; the first vector is arbitrary in the full physical LLL. -/
theorem weighted_rawPlaneJet_pairing_summable (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (a : ℝ) (ha : 0 < a) (R : ℂ) (h : LLL G theta 1) :
    Summable (fun j : ℕ => thermalRootRatio a ^ (j+1) *
      ‖inner ℂ h (rawPlaneJet G theta j R)‖) := by
  have hs := (weighted_rawPlaneJet_norm_summable G theta hG a ha R).mul_left ‖h‖
  apply Summable.of_nonneg_of_le
    (fun j => mul_nonneg (pow_nonneg (thermalRootRatio_pos_lt_one a ha).1.le _) (norm_nonneg _))
    (fun j => ?_) hs
  calc
    _ ≤ thermalRootRatio a ^ (j+1) * (‖h‖ * ‖rawPlaneJet G theta j R‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _)
        (pow_nonneg (thermalRootRatio_pos_lt_one a ha).1.le _)
    _ = _ := by ring

end TorusLean.Shared.CoherentThermalSummability
