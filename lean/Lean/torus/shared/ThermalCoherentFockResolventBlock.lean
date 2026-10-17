import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Uniform real resolvent bounds from the exact sector norm-square form
estimate. The centered-square proof avoids any dimension-dependent estimate.
The sector estimate is an explicit hypothesis, not an asserted physical gap. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFockResolventBlock
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def shiftedBlock (H : E →L[ℂ] E) (lambda : ℝ) : E →L[ℂ] E :=
  H - (lambda : ℂ) • ContinuousLinearMap.id ℂ E

@[simp] theorem shiftedBlock_apply (H : E →L[ℂ] E) (lambda : ℝ) (x : E) :
    shiftedBlock H lambda x = H x - (lambda : ℂ) • x := rfl

private theorem shifted_norm_sq (H : E →L[ℂ] E) (mu : ℝ) (x : E) :
    ‖shiftedBlock H mu x‖^2 =
      ‖H x‖^2 - 2*mu*(inner ℂ x (H x)).re + mu^2*‖x‖^2 := by
  have h := norm_sub_sq (𝕜 := ℂ) (H x) ((mu : ℂ) • x)
  change ‖H x-(mu : ℂ) • x‖^2 =
    ‖H x‖^2 - 2*(inner ℂ (H x) ((mu : ℂ) • x)).re + ‖(mu : ℂ) • x‖^2 at h
  rw [inner_smul_right,norm_smul] at h
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs] at h
  have hr : (inner ℂ (H x) x).re = (inner ℂ x (H x)).re :=
    inner_re_symm (𝕜 := ℂ) (H x) x
  change ‖H x-(mu : ℂ) • x‖^2 = _
  rw [h,hr]
  ring

/-- At the center of the forbidden interval, the quadratic form estimate
itself gives the required uniform lower singular-value bound. -/
theorem centered_block_coercive (H : E →L[ℂ] E) (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hform : ∀ x, gamma*(inner ℂ x (H x)).re ≤ ‖H x‖^2) (x : E) :
    (gamma/2)*‖x‖ ≤ ‖shiftedBlock H (gamma/2) x‖ := by
  apply (sq_le_sq₀ (mul_nonneg (by positivity) (norm_nonneg x)) (norm_nonneg _)).mp
  rw [shifted_norm_sq]
  nlinarith [hform x]

/-- The same dimension-independent estimate throughout the open interval. -/
theorem shifted_block_coercive (H : E →L[ℂ] E) (gamma lambda : ℝ)
    (hlambda : 0 < lambda) (hlambda' : lambda < gamma)
    (hform : ∀ x, gamma*(inner ℂ x (H x)).re ≤ ‖H x‖^2) (x : E) :
    min lambda (gamma-lambda)*‖x‖ ≤ ‖shiftedBlock H lambda x‖ := by
  have hc := centered_block_coercive H gamma (by linarith) hform x
  have he : shiftedBlock H (gamma/2) x =
      shiftedBlock H lambda x + ((lambda-gamma/2 : ℝ) : ℂ) • x := by
    simp only [shiftedBlock_apply,Complex.ofReal_sub,Complex.ofReal_div,Complex.ofReal_ofNat]
    module
  have ht := norm_add_le (shiftedBlock H lambda x) (((lambda-gamma/2 : ℝ) : ℂ) • x)
  rw [← he,norm_smul] at ht
  simp only [Complex.norm_real,Real.norm_eq_abs] at ht
  by_cases h : lambda ≤ gamma/2
  · rw [abs_of_nonpos (by linarith)] at ht
    rw [min_eq_left (by linarith)]
    nlinarith
  · rw [abs_of_nonneg (by linarith)] at ht
    rw [min_eq_right (by linarith)]
    nlinarith

private theorem shifted_block_injective (H : E →L[ℂ] E) (gamma lambda : ℝ)
    (hlambda : 0 < lambda) (hlambda' : lambda < gamma)
    (hform : ∀ x, gamma*(inner ℂ x (H x)).re ≤ ‖H x‖^2) :
    Function.Injective (shiftedBlock H lambda) := by
  intro x y hxy
  have hz : shiftedBlock H lambda (x-y)=0 := by rw [map_sub,hxy,sub_self]
  have h := shifted_block_coercive H gamma lambda hlambda hlambda' hform (x-y)
  rw [hz,norm_zero] at h
  have hd : 0 < min lambda (gamma-lambda) := lt_min hlambda (sub_pos.mpr hlambda')
  have hn : ‖x-y‖=0 := by nlinarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

variable [FiniteDimensional ℂ E]

/-- The inverse is obtained from genuine finite-dimensional bijectivity. -/
def blockResolvent (H : E →L[ℂ] E) (gamma lambda : ℝ)
    (hlambda : 0 < lambda) (hlambda' : lambda < gamma)
    (hform : ∀ x, gamma*(inner ℂ x (H x)).re ≤ ‖H x‖^2) : E →L[ℂ] E :=
  (LinearEquiv.ofInjectiveEndo (shiftedBlock H lambda).toLinearMap
    (shifted_block_injective H gamma lambda hlambda hlambda' hform)).toContinuousLinearEquiv.symm

theorem blockResolvent_right_inverse (H : E →L[ℂ] E) (gamma lambda : ℝ)
    (hlambda : 0 < lambda) (hlambda' : lambda < gamma)
    (hform : ∀ x, gamma*(inner ℂ x (H x)).re ≤ ‖H x‖^2) (x : E) :
    shiftedBlock H lambda (blockResolvent H gamma lambda hlambda hlambda' hform x)=x :=
  (LinearEquiv.ofInjectiveEndo (shiftedBlock H lambda).toLinearMap
    (shifted_block_injective H gamma lambda hlambda hlambda' hform)).apply_symm_apply x

theorem blockResolvent_left_inverse (H : E →L[ℂ] E) (gamma lambda : ℝ)
    (hlambda : 0 < lambda) (hlambda' : lambda < gamma)
    (hform : ∀ x, gamma*(inner ℂ x (H x)).re ≤ ‖H x‖^2) (x : E) :
    blockResolvent H gamma lambda hlambda hlambda' hform (shiftedBlock H lambda x)=x :=
  (LinearEquiv.ofInjectiveEndo (shiftedBlock H lambda).toLinearMap
    (shifted_block_injective H gamma lambda hlambda hlambda' hform)).symm_apply_apply x

theorem blockResolvent_norm_le (H : E →L[ℂ] E) (gamma lambda : ℝ)
    (hlambda : 0 < lambda) (hlambda' : lambda < gamma)
    (hform : ∀ x, gamma*(inner ℂ x (H x)).re ≤ ‖H x‖^2) (x : E) :
    ‖blockResolvent H gamma lambda hlambda hlambda' hform x‖ ≤
      (min lambda (gamma-lambda))⁻¹*‖x‖ := by
  have h := shifted_block_coercive H gamma lambda hlambda hlambda' hform
    (blockResolvent H gamma lambda hlambda hlambda' hform x)
  rw [blockResolvent_right_inverse] at h
  have hd : 0 < min lambda (gamma-lambda) := lt_min hlambda (sub_pos.mpr hlambda')
  exact (le_div_iff₀ hd).mpr (by simpa only [mul_comm] using h) |>.trans_eq (div_eq_inv_mul _ _)

end TorusLean.Shared.ThermalCoherentFockResolventBlock
