import torus.shared.ChargeTwoIsometry
import torus.shared.BosonPlaneKernelProduct

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ChargeFourScaling
open TorusLean.Geometry
open TorusLean.Shared.ChargeTwoScaling
open scoped ComplexConjugate

theorem scaled_gaussian (z : ℂ) :
    gaussianFactor 2 ((scale : ℂ) * z) = gaussianFactor 4 z := by
  unfold gaussianFactor
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_one,
    Complex.ofReal_ofNat]
  have hs := scale_complex_sq
  linear_combination -(z * conj z) * hs

theorem scaled_magneticExponent (z x : ℂ) :
    magneticExponent 2 ((scale : ℂ) * z) ((scale : ℂ) * x) =
      magneticExponent 4 z x := by
  unfold magneticExponent
  simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_one, one_mul,
    Complex.ofReal_ofNat]
  have hs := scale_complex_sq
  linear_combination (z * conj x - conj z * x) * hs

/-- Pullback by the real dilation intertwines the original physical
charge-two and charge-four magnetic translations. -/
theorem scaled_magneticTranslate (x z : ℂ) (f : ℂ → ℂ) :
    magneticTranslate 2 ((scale : ℂ) * x) f ((scale : ℂ) * z) =
      magneticTranslate 4 x (fun w => f ((scale : ℂ) * w)) z := by
  unfold magneticTranslate
  rw [scaled_magneticExponent]
  congr 1
  congr 1
  ring

theorem scale_mul_div (z : ℂ) : (scale : ℂ) * (z / (scale : ℂ)) = z := by
  have hn : (scale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr scale_pos.ne'
  field_simp

theorem gaussianHolomorphic_pullback_iff (f : ℂ → ℂ) :
    IsGaussianHolomorphic 2 f ↔
      IsGaussianHolomorphic 4 (fun z => f ((scale : ℂ) * z)) := by
  constructor
  · rintro ⟨F, hF, hf⟩
    refine ⟨fun z => F ((scale : ℂ) * z), hF.comp (differentiable_id.const_mul (scale : ℂ)), ?_⟩
    intro z
    change f ((scale : ℂ) * z) = gaussianFactor 4 z * F ((scale : ℂ) * z)
    rw [hf, scaled_gaussian]
  · rintro ⟨F, hF, hf⟩
    refine ⟨fun w => F (w / (scale : ℂ)), hF.comp (differentiable_id.div_const _), ?_⟩
    intro w
    have h := hf (w / (scale : ℂ))
    change f ((scale : ℂ) * (w / (scale : ℂ))) = _ at h
    rw [scale_mul_div, ← scaled_gaussian, scale_mul_div] at h
    exact h

theorem latticeBoundary_pullback_iff (G : Geometry) (theta : Twist) (f : ℂ → ℂ) :
    HasLatticeBoundary (scaledGeometry G).M 2 (scaledGeometry G).omega1
      (scaledGeometry G).omega2 (scaledTwist theta).theta1 (scaledTwist theta).theta2 f ↔
    HasLatticeBoundary G.M 4 G.omega1 G.omega2 theta.theta1 theta.theta2
      (fun z => f ((scale : ℂ) * z)) := by
  unfold HasLatticeBoundary HasMagneticEigencharacter
  constructor
  · intro hf p
    funext z
    have h := congrFun (hf p) ((scale : ℂ) * z)
    norm_num only [Nat.cast_ofNat, Nat.cast_ofNat] at h ⊢
    simpa only [scaled_period, scaled_character, ← pow_mul, show 2*2=4 from rfl, scaled_magneticTranslate] using h
  · intro hf p
    funext w
    have h := congrFun (hf p) (w / (scale : ℂ))
    norm_num only [Nat.cast_ofNat, Nat.cast_ofNat] at h ⊢
    change magneticTranslate 4 _ _ _ = latticeChi G.M theta.theta1 theta.theta2 p ^ 4 * f ((scale : ℂ) * (w / (scale : ℂ))) at h
    rw [← scaled_magneticTranslate, scale_mul_div] at h
    simpa only [scaled_period, scaled_character, ← pow_mul, show 2*2=4 from rfl] using h

/-- Actual full section-carrier dilation, before proving its norm identity. -/
def pullbackLinear (G : Geometry) (theta : Twist) :
    LLL (scaledGeometry G) (scaledTwist theta) 2 →ₗ[ℂ] LLL G theta 4 where
  toFun f := ⟨fun z => f.val ((scale : ℂ) * z), by
    have hf : IsGaussianHolomorphic 2 f.val := by simpa only [Nat.cast_ofNat] using f.property.1
    change IsGaussianHolomorphic 4 (fun z => f.val ((scale : ℂ) * z)) ∧ _
    exact ⟨(gaussianHolomorphic_pullback_iff f.val).mp hf,
      (latticeBoundary_pullback_iff G theta f.val).mp f.property.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def pushforwardLinear (G : Geometry) (theta : Twist) :
    LLL G theta 4 →ₗ[ℂ] LLL (scaledGeometry G) (scaledTwist theta) 2 where
  toFun f := ⟨fun w => f.val (w / (scale : ℂ)), by
    have hfun : (fun z => f.val (((scale : ℂ) * z) / (scale : ℂ))) = f.val := by
      funext z
      have hn : (scale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr scale_pos.ne'
      field_simp
    simp only [rawLLLSubmodule, Nat.cast_ofNat]
    constructor
    · apply (gaussianHolomorphic_pullback_iff _).mpr
      rw [hfun]
      simpa only [Nat.cast_ofNat] using f.property.1
    · apply (latticeBoundary_pullback_iff G theta _).mpr
      rw [hfun]
      exact f.property.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def scalingLinearEquiv (G : Geometry) (theta : Twist) :
    LLL (scaledGeometry G) (scaledTwist theta) 2 ≃ₗ[ℂ] LLL G theta 4 where
  toLinearMap := pullbackLinear G theta
  invFun := pushforwardLinear G theta
  left_inv f := by
    apply Subtype.ext
    funext w
    change f.val ((scale : ℂ) * (w / (scale : ℂ))) = f.val w
    rw [scale_mul_div]
  right_inv f := by
    apply Subtype.ext
    funext z
    change f.val (((scale : ℂ) * z) / (scale : ℂ)) = f.val z
    have hn : (scale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr scale_pos.ne'
    field_simp

theorem scalingLinearEquiv_apply (G : Geometry) (theta : Twist)
    (f : LLL (scaledGeometry G) (scaledTwist theta) 2) (z : ℂ) :
    (scalingLinearEquiv G theta f).val z = f.val ((scale : ℂ) * z) := rfl

theorem scalingLinearEquiv_symm_apply (G : Geometry) (theta : Twist)
    (f : LLL G theta 4) (w : ℂ) :
    ((scalingLinearEquiv G theta).symm f).val w = f.val (w / (scale : ℂ)) := rfl


open MeasureTheory TorusLean.Shared.ChargeTwoIsometry

theorem dilation_measurePreserving (G : Geometry) :
    MeasurePreserving dilation (cellMeasure G 4) (cellMeasure (scaledGeometry G) 2) := by
  refine ⟨dilation.continuous.measurable, ?_⟩
  rw [cellMeasure, Measure.map_smul _ dilation.continuous.measurable.aemeasurable,
    dilation_map_restricted, smul_smul]
  unfold cellMeasure
  congr 1
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  norm_num
  ring

theorem scalingLinearEquiv_norm (G : Geometry) (theta : Twist)
    (f : LLL (scaledGeometry G) (scaledTwist theta) 2) :
    ‖scalingLinearEquiv G theta f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [lll_norm_sq_eq_cellIntegral, lll_norm_sq_eq_cellIntegral]
  have h := (dilation_measurePreserving G).integral_comp
    dilation.toMeasurableEquiv.measurableEmbedding (fun w => ‖f.val w‖^2)
  simpa only [dilation_apply, scalingLinearEquiv_apply] using h

def scalingLinearIsometryEquiv (G : Geometry) (theta : Twist) :
    LLL (scaledGeometry G) (scaledTwist theta) 2 ≃ₗᵢ[ℂ] LLL G theta 4 :=
  { scalingLinearEquiv G theta with norm_map' := scalingLinearEquiv_norm G theta }

theorem evaluationKernel_four_scaled (G : Geometry) (theta : Twist) (S : ℂ) :
    scalingLinearIsometryEquiv G theta
      (evaluationKernel (scaledGeometry G) (scaledTwist theta) 2 ((scale : ℂ)*S)) =
      evaluationKernel G theta 4 S := by
  apply ext_inner_right ℂ
  intro f
  obtain ⟨g,rfl⟩ := (scalingLinearIsometryEquiv G theta).surjective f
  rw [(scalingLinearIsometryEquiv G theta).inner_map_map,
    evaluationKernel_reproduces, evaluationKernel_reproduces]
  rfl

theorem evaluationKernel_four_periodization (G : Geometry) (theta : Twist) (S z : ℂ) :
    (evaluationKernel G theta 4 S).val z =
      magneticPeriodization G.M 4 G.omega1 G.omega2 theta.theta1 theta.theta2
        (magneticTranslate 4 S (gaussianFactor 4)) z := by
  rw [← evaluationKernel_four_scaled]
  change (evaluationKernel (scaledGeometry G) (scaledTwist theta) 2 ((scale : ℂ)*S)).val
    ((scale : ℂ)*z) = _
  rw [TorusLean.Shared.BosonPlaneKernelProduct.evaluationKernel_two_periodization]
  unfold magneticPeriodization
  apply tsum_congr
  intro p
  simp only [magneticImage, Nat.cast_ofNat, scaled_character, ← pow_mul,
    show 2*2=4 from rfl, scaled_period, scaled_magneticTranslate, scaled_gaussian]

#print axioms scaled_gaussian
#print axioms scaled_magneticExponent
#print axioms scaled_magneticTranslate
#print axioms gaussianHolomorphic_pullback_iff
#print axioms latticeBoundary_pullback_iff
#print axioms scalingLinearEquiv_apply
#print axioms scalingLinearEquiv_symm_apply
#print axioms dilation_measurePreserving
#print axioms scalingLinearEquiv_norm
#print axioms evaluationKernel_four_scaled
#print axioms evaluationKernel_four_periodization
end TorusLean.Shared.ChargeFourScaling
