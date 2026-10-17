import torus.shared.ThermalCoherentFermionAnchoredCoefficients

/-! Exact two surviving m=1 pair coefficients of the anchored degree-l+1
Slater column. These are derived from the original factorial formula,
not supplied as normalization data. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchored
open TorusLean.Shared.FermionRelativeFrame

private theorem sqrt_two_pow_sq (p : ℕ) :
    ((Real.sqrt (2:ℝ))^p)^2=(2:ℝ)^p := by
  rw [← pow_mul,Nat.mul_comm p 2,pow_mul,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]

/-- Magnitude of the occupied (0,l) coefficient, written with l=p+1. -/
theorem anchored_zero_pair_weight (p : ℕ) :
    (p+1:ℝ)*paperPairWeight p 0 (p+1) = Real.sqrt (p+1:ℝ)/(Real.sqrt (2:ℝ))^p := by
  have hf : (p.factorial:ℝ)≠0 := by positivity
  have h2 : ((2:ℝ)^p)≠0 := by positivity
  have hp : (p+1:ℝ)≠0 := by positivity
  apply (sq_eq_sq₀ (by unfold paperPairWeight; positivity) (by positivity)).mp
  rw [mul_pow,div_pow,sqrt_two_pow_sq,Real.sq_sqrt (by positivity : (0:ℝ)≤p+1)]
  unfold paperPairWeight
  rw [Real.sq_sqrt (by positivity)]
  simp only [Nat.factorial_zero,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  field_simp

/-- The second occupied-pair factorial ratio has no residual factorial. -/
theorem anchored_one_pair_weight (p : ℕ) :
    paperPairWeight p 1 p = (Real.sqrt (2:ℝ))⁻¹^p := by
  have hf : (p.factorial:ℝ)≠0 := by positivity
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  change (Real.sqrt ((p.factorial:ℝ)/(2^p*((1:ℕ).factorial:ℝ)*(p.factorial:ℝ))))^2 = _
  rw [Real.sq_sqrt (by positivity),inv_pow,inv_pow,sqrt_two_pow_sq]
  simp only [Nat.factorial_one,Nat.cast_one,mul_one]
  field_simp

/-- Signed (0,l) entry in precisely the paper's pair orientation. -/
theorem planePairCoefficient_zero_closed (p : ℕ) :
    planePairCoefficient p 0 (p+1) = -Real.sqrt (p+1:ℝ)/(Real.sqrt (2:ℝ))^p := by
  rw [planePairCoefficient_zero_orbital,if_pos rfl]
  simp only [Nat.cast_add,Nat.cast_one]
  rw [neg_mul,anchored_zero_pair_weight,neg_div]

/-- Signed (1,l) entry, including its vanishing l=1 value. -/
theorem planePairCoefficient_one_closed (p : ℕ) :
    planePairCoefficient p 1 p = (1-(p:ℝ))/(Real.sqrt (2:ℝ))^p := by
  simp only [planePairCoefficient_one_orbital,if_true,anchored_one_pair_weight,inv_pow,div_eq_mul_inv]

end TorusLean.Shared.ThermalCoherentFermionAnchored
