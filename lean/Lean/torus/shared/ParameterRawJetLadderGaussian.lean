import torus.shared.ParameterRawJetLadderCalculus

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ParameterRawJetLadder
open TorusLean.Geometry TorusLean.Shared.ParameterCellAdjoint
open scoped ComplexConjugate

theorem parameterLower_const_mul (k : ℕ) (c : ℂ) (f : ℂ → ℂ)
    (hf : Differentiable ℝ f) (R : ℂ) :
    parameterLower k (fun z => c*f z) R = c*parameterLower k f R := by
  unfold parameterLower
  rw [(wirtinger_const_mul c f hf R).1]
  ring

theorem parameterRaise_const_mul (k : ℕ) (c : ℂ) (f : ℂ → ℂ)
    (hf : Differentiable ℝ f) (R : ℂ) :
    parameterRaise k (fun z => c*f z) R = c*parameterRaise k f R := by
  unfold parameterRaise
  rw [(wirtinger_const_mul c f hf R).2]
  ring

/-- Exact cancellation of the dual charge-one Gaussian in the lowering action. -/
theorem parameterLower_conj_gaussian (F : ℂ → ℂ) (hF : Differentiable ℝ F) (R : ℂ) :
    parameterLower 1 (fun z => conj (gaussianFactor 1 z * F z)) R =
      -conj (gaussianFactor 1 R * parameterWirtingerBar F R) := by
  have hg : Differentiable ℝ (gaussianFactor 1) := by
    unfold gaussianFactor
    fun_prop
  unfold parameterLower
  rw [(wirtinger_conj (fun z => gaussianFactor 1 z * F z) (hg.mul hF) R).1,
    wirtingerBar_mul (gaussianFactor 1) F hg hF R, (wirtinger_gaussian R).2]
  simp only [Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, div_one,
    map_add, map_mul, map_div₀, map_neg, map_ofNat, Complex.conj_conj]
  ring

/-- Exact dual raising action, retaining the magnetic centered polynomial. -/
theorem parameterRaise_conj_gaussian (F : ℂ → ℂ) (hF : Differentiable ℝ F) (R : ℂ) :
    parameterRaise 1 (fun z => conj (gaussianFactor 1 z * F z)) R =
      conj (gaussianFactor 1 R * (parameterWirtinger F R - conj R * F R)) := by
  have hg : Differentiable ℝ (gaussianFactor 1) := by
    unfold gaussianFactor
    fun_prop
  unfold parameterRaise
  rw [(wirtinger_conj (fun z => gaussianFactor 1 z * F z) (hg.mul hF) R).2,
    wirtinger_mul (gaussianFactor 1) F hg hF R, (wirtinger_gaussian R).1]
  simp only [Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, div_one,
    map_add, map_sub, map_mul, map_div₀, map_neg, map_ofNat, Complex.conj_conj]
  ring

end TorusLean.Shared.ParameterRawJetLadder
