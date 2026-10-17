import torus.shared.ParameterRawJetLadderBasic

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ParameterRawJetLadder
open TorusLean.Geometry TorusLean.Shared.ParameterCellAdjoint
open scoped ComplexConjugate ContDiff BigOperators

theorem wirtinger_mul (f g : ℂ → ℂ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (R : ℂ) :
    parameterWirtinger (fun z => f z * g z) R =
      parameterWirtinger f R * g R + f R * parameterWirtinger g R := by
  unfold parameterWirtinger
  rw [fderiv_fun_mul (hf R) (hg R)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem wirtingerBar_mul (f g : ℂ → ℂ) (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (R : ℂ) :
    parameterWirtingerBar (fun z => f z * g z) R =
      parameterWirtingerBar f R * g R + f R * parameterWirtingerBar g R := by
  unfold parameterWirtingerBar
  rw [fderiv_fun_mul (hf R) (hg R)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem wirtinger_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) (R : ℂ) :
    parameterWirtinger (fun z => ∑ i ∈ s, f i z) R =
      ∑ i ∈ s, parameterWirtinger (f i) R := by
  unfold parameterWirtinger
  rw [fderiv_fun_sum (fun i hi => hf i hi R)]
  simp only [sum_apply, Finset.mul_sum]
  simp only [div_eq_mul_inv, Finset.sum_sub_distrib, Finset.sum_mul, sub_mul]

theorem wirtingerBar_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) (R : ℂ) :
    parameterWirtingerBar (fun z => ∑ i ∈ s, f i z) R =
      ∑ i ∈ s, parameterWirtingerBar (f i) R := by
  unfold parameterWirtingerBar
  rw [fderiv_fun_sum (fun i hi => hf i hi R)]
  simp only [sum_apply, Finset.mul_sum]
  simp only [div_eq_mul_inv, Finset.sum_add_distrib, Finset.sum_mul, add_mul]

theorem wirtinger_holomorphic (f : ℂ → ℂ) (hf : Differentiable ℂ f) (R : ℂ) :
    parameterWirtinger f R = deriv f R ∧ parameterWirtingerBar f R = 0 := by
  have hx : (fderiv ℝ f R) 1 = deriv f R := by
    rw [(hf R).fderiv_restrictScalars ℝ]
    change (fderiv ℂ f R) 1 = _
    simp
  have hy : (fderiv ℝ f R) Complex.I = Complex.I * deriv f R := by
    rw [(hf R).fderiv_restrictScalars ℝ]
    change (fderiv ℂ f R) Complex.I = _
    simp
  simp only [parameterWirtinger, parameterWirtingerBar, hx, hy, ← mul_assoc,
    Complex.I_mul_I]
  constructor <;> ring

theorem wirtinger_conj (f : ℂ → ℂ) (hf : Differentiable ℝ f) (R : ℂ) :
    parameterWirtinger (fun z => conj (f z)) R = conj (parameterWirtingerBar f R) ∧
    parameterWirtingerBar (fun z => conj (f z)) R = conj (parameterWirtinger f R) := by
  have hd := (Complex.conjCLE.hasFDerivAt.comp R (hf R).hasFDerivAt).fderiv
  change fderiv ℝ (fun z => conj (f z)) R = _ at hd
  simp only [parameterWirtinger, parameterWirtingerBar, hd,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, map_div₀, map_add, map_sub, map_mul, map_ofNat, Complex.conj_I]
  constructor <;> ring

theorem wirtinger_pow (f : ℂ → ℂ) (hf : Differentiable ℝ f) (n : ℕ) (R : ℂ) :
    parameterWirtinger (fun z => f z^n) R = (n:ℂ)*f R^(n-1)*parameterWirtinger f R ∧
    parameterWirtingerBar (fun z => f z^n) R = (n:ℂ)*f R^(n-1)*parameterWirtingerBar f R := by
  simp only [parameterWirtinger, parameterWirtingerBar, fderiv_fun_pow n (hf R),
    smul_apply, smul_eq_mul, nsmul_eq_mul]
  constructor <;> ring

theorem wirtinger_const_mul (c : ℂ) (f : ℂ → ℂ) (hf : Differentiable ℝ f) (R : ℂ) :
    parameterWirtinger (fun z => c*f z) R = c*parameterWirtinger f R ∧
    parameterWirtingerBar (fun z => c*f z) R = c*parameterWirtingerBar f R := by
  simp only [parameterWirtinger, parameterWirtingerBar, fderiv_const_mul (hf R) c,
    smul_apply, smul_eq_mul]
  constructor <;> ring

theorem wirtinger_neg_conj (R : ℂ) :
    parameterWirtinger (fun z => -conj z) R = 0 ∧
      parameterWirtingerBar (fun z => -conj z) R = -1 := by
  have hd := (Complex.conjCLE.hasFDerivAt.neg).fderiv (x := R)
  change fderiv ℝ (fun z : ℂ => -conj z) R = -Complex.conjCLE.toContinuousLinearMap at hd
  simp only [parameterWirtinger, parameterWirtingerBar, hd, neg_apply,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_one, Complex.conj_I]
  constructor <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

theorem wirtinger_gaussian (R : ℂ) :
    parameterWirtinger (gaussianFactor 1) R = -conj R/2*gaussianFactor 1 R ∧
    parameterWirtingerBar (gaussianFactor 1) R = -R/2*gaussianFactor 1 R := by
  have heq : gaussianFactor 1 = fun z : ℂ => Complex.exp ((-(1:ℂ)/2)*(z*conj z)) := by
    funext z
    simp only [gaussianFactor, Complex.ofReal_one]
    congr 1; ring
  have hd := (((hasFDerivAt_id R).mul Complex.conjCLE.hasFDerivAt).const_smul (-(1:ℂ)/2)).cexp.fderiv
  change fderiv ℝ (fun z : ℂ => Complex.exp ((-(1:ℂ)/2)*(z*conj z))) R = _ at hd
  dsimp only [Pi.smul_apply, Pi.mul_apply, id_eq, smul_eq_mul] at hd
  rw [heq]
  simp only [parameterWirtinger, parameterWirtingerBar, hd, add_apply, smul_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearEquiv.coe_coe,
    Complex.conjCLE_apply, map_one, Complex.conj_I, smul_eq_mul]
  constructor <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

end TorusLean.Shared.ParameterRawJetLadder
