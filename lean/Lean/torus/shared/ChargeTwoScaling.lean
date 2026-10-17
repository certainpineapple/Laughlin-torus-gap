import torus.shared.CellHilbert
import torus.shared.PlaneJetGramBounds

set_option autoImplicit false
noncomputable section

namespace TorusLean.Shared.ChargeTwoScaling

open TorusLean.Geometry
open scoped ComplexConjugate

def scale : ℝ := Real.sqrt 2

theorem scale_pos : 0 < scale := by unfold scale; positivity

theorem scale_sq : scale^2 = 2 := by unfold scale; norm_num

theorem scale_complex_sq : (scale : ℂ)^2 = 2 := by exact_mod_cast scale_sq

/-- The enlarged physical lattice, with doubled integral flux. -/
def scaledGeometry (G : Geometry) : Geometry where
  M := 2 * G.M
  flux_pos := Nat.mul_pos (by decide) G.flux_pos
  omega1 := (scale : ℂ) * G.omega1
  omega2 := (scale : ℂ) * G.omega2
  area := by
    calc
      _ = (((scale : ℂ)^2) * (conj G.omega1 * G.omega2)).im := by
        congr 1
        simp only [map_mul, Complex.conj_ofReal]
        ring
      _ = _ := by
        rw [scale_complex_sq]
        rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by rfl, Complex.mul_im]
        simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
        rw [G.area]
        push_cast
        ring

def scaledTwist (theta : Twist) : Twist := ⟨2 * theta.theta1, 2 * theta.theta2⟩

theorem scaled_period (G : Geometry) (p : ℤ × ℤ) :
    latticePeriod (scaledGeometry G).omega1 (scaledGeometry G).omega2 p =
      (scale : ℂ) * latticePeriod G.omega1 G.omega2 p := by
  unfold latticePeriod scaledGeometry
  ring

/-- Exact semicharacter, including the integral-flux parity term. -/
theorem scaled_character (G : Geometry) (theta : Twist) (p : ℤ × ℤ) :
    latticeChi (scaledGeometry G).M (scaledTwist theta).theta1 (scaledTwist theta).theta2 p =
      latticeChi G.M theta.theta1 theta.theta2 p ^ 2 := by
  unfold latticeChi
  rw [pow_two, ← Complex.exp_add]
  congr 1
  unfold twistExponent scaledGeometry scaledTwist
  push_cast
  ring

theorem scaled_gaussian (z : ℂ) :
    gaussianFactor 1 ((scale : ℂ) * z) = gaussianFactor 2 z := by
  unfold gaussianFactor
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_one,
    Complex.ofReal_ofNat]
  have hs := scale_complex_sq
  linear_combination -(z * conj z) / 2 * hs

theorem scaled_magneticExponent (z x : ℂ) :
    magneticExponent 1 ((scale : ℂ) * z) ((scale : ℂ) * x) =
      magneticExponent 2 z x := by
  unfold magneticExponent
  simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_one, one_mul,
    Complex.ofReal_ofNat]
  have hs := scale_complex_sq
  linear_combination (z * conj x - conj z * x) / 2 * hs

/-- Pullback by the real dilation intertwines the original physical
charge-one and charge-two magnetic translations. -/
theorem scaled_magneticTranslate (x z : ℂ) (f : ℂ → ℂ) :
    magneticTranslate 1 ((scale : ℂ) * x) f ((scale : ℂ) * z) =
      magneticTranslate 2 x (fun w => f ((scale : ℂ) * w)) z := by
  unfold magneticTranslate
  rw [scaled_magneticExponent]
  congr 1
  congr 1
  ring

theorem scale_mul_div (z : ℂ) : (scale : ℂ) * (z / (scale : ℂ)) = z := by
  have hn : (scale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr scale_pos.ne'
  field_simp

theorem gaussianHolomorphic_pullback_iff (f : ℂ → ℂ) :
    IsGaussianHolomorphic 1 f ↔
      IsGaussianHolomorphic 2 (fun z => f ((scale : ℂ) * z)) := by
  constructor
  · rintro ⟨F, hF, hf⟩
    refine ⟨fun z => F ((scale : ℂ) * z), hF.comp (differentiable_id.const_mul (scale : ℂ)), ?_⟩
    intro z
    change f ((scale : ℂ) * z) = gaussianFactor 2 z * F ((scale : ℂ) * z)
    rw [hf, scaled_gaussian]
  · rintro ⟨F, hF, hf⟩
    refine ⟨fun w => F (w / (scale : ℂ)), hF.comp (differentiable_id.div_const _), ?_⟩
    intro w
    have h := hf (w / (scale : ℂ))
    change f ((scale : ℂ) * (w / (scale : ℂ))) = _ at h
    rw [scale_mul_div, ← scaled_gaussian, scale_mul_div] at h
    exact h

theorem latticeBoundary_pullback_iff (G : Geometry) (theta : Twist) (f : ℂ → ℂ) :
    HasLatticeBoundary (scaledGeometry G).M 1 (scaledGeometry G).omega1
      (scaledGeometry G).omega2 (scaledTwist theta).theta1 (scaledTwist theta).theta2 f ↔
    HasLatticeBoundary G.M 2 G.omega1 G.omega2 theta.theta1 theta.theta2
      (fun z => f ((scale : ℂ) * z)) := by
  unfold HasLatticeBoundary HasMagneticEigencharacter
  constructor
  · intro hf p
    funext z
    have h := congrFun (hf p) ((scale : ℂ) * z)
    norm_num only [Nat.cast_one, Nat.cast_ofNat] at h ⊢
    simpa only [scaled_period, scaled_character, pow_one, scaled_magneticTranslate] using h
  · intro hf p
    funext w
    have h := congrFun (hf p) (w / (scale : ℂ))
    norm_num only [Nat.cast_one, Nat.cast_ofNat] at h ⊢
    change magneticTranslate 2 _ _ _ = latticeChi G.M theta.theta1 theta.theta2 p ^ 2 * f ((scale : ℂ) * (w / (scale : ℂ))) at h
    rw [← scaled_magneticTranslate, scale_mul_div] at h
    simpa only [scaled_period, scaled_character, pow_one] using h

/-- Actual full section-carrier dilation, before proving its norm identity. -/
def pullbackLinear (G : Geometry) (theta : Twist) :
    LLL (scaledGeometry G) (scaledTwist theta) 1 →ₗ[ℂ] LLL G theta 2 where
  toFun f := ⟨fun z => f.val ((scale : ℂ) * z), by
    have hf : IsGaussianHolomorphic 1 f.val := by simpa only [Nat.cast_one] using f.property.1
    change IsGaussianHolomorphic 2 (fun z => f.val ((scale : ℂ) * z)) ∧ _
    exact ⟨(gaussianHolomorphic_pullback_iff f.val).mp hf,
      (latticeBoundary_pullback_iff G theta f.val).mp f.property.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def pushforwardLinear (G : Geometry) (theta : Twist) :
    LLL G theta 2 →ₗ[ℂ] LLL (scaledGeometry G) (scaledTwist theta) 1 where
  toFun f := ⟨fun w => f.val (w / (scale : ℂ)), by
    have hfun : (fun z => f.val (((scale : ℂ) * z) / (scale : ℂ))) = f.val := by
      funext z
      have hn : (scale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr scale_pos.ne'
      field_simp
    simp only [rawLLLSubmodule, Nat.cast_one]
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
    LLL (scaledGeometry G) (scaledTwist theta) 1 ≃ₗ[ℂ] LLL G theta 2 where
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
    (f : LLL (scaledGeometry G) (scaledTwist theta) 1) (z : ℂ) :
    (scalingLinearEquiv G theta f).val z = f.val ((scale : ℂ) * z) := rfl

theorem scalingLinearEquiv_symm_apply (G : Geometry) (theta : Twist)
    (f : LLL G theta 2) (w : ℂ) :
    ((scalingLinearEquiv G theta).symm f).val w = f.val (w / (scale : ℂ)) := rfl

theorem scaled_systole_lower (G : Geometry) (L : ℝ)
    (hL : L ≤ TorusLean.Fermion.LatticePacking.systole G) :
    scale * L ≤ TorusLean.Fermion.LatticePacking.systole (scaledGeometry G) := by
  apply (TorusLean.Fermion.LatticePacking.systole_ge_iff _ _).mpr
  intro p hp
  have h := mul_le_mul_of_nonneg_left
    ((TorusLean.Fermion.LatticePacking.systole_ge_iff G L).mp hL p hp) scale_pos.le
  simpa only [TorusLean.Fermion.LatticePacking.period, scaled_period, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos scale_pos] using h

#print axioms scaledGeometry
#print axioms scaledTwist
#print axioms scale_mul_div
#print axioms scaled_systole_lower
#print axioms gaussianHolomorphic_pullback_iff
#print axioms latticeBoundary_pullback_iff
#print axioms pullbackLinear
#print axioms pushforwardLinear
#print axioms scalingLinearEquiv
#print axioms scalingLinearEquiv_apply
#print axioms scalingLinearEquiv_symm_apply
#print axioms scale_pos
#print axioms scale_sq
#print axioms scale_complex_sq
#print axioms scaled_period
#print axioms scaled_character
#print axioms scaled_gaussian
#print axioms scaled_magneticExponent
#print axioms scaled_magneticTranslate

end TorusLean.Shared.ChargeTwoScaling
