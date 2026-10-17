import torus.shared.RelativeJetMapFamily
import torus.shared.ChargeTwoIsometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.RelativeJetMap
open TorusLean.Geometry TorusLean.Shared.NormalJetBridge
open TorusLean.Shared.ChargeTwoScaling TorusLean.Shared.ChargeTwoIsometry
open TorusLean.Shared.PlaneJetReproducing TorusLean.Shared.PlaneJetMembership
open TorusLean.Shared.GroundJetReproducing
open scoped TensorProduct ComplexConjugate BigOperators

/-- The actual charge-two canonical derivative obtained by the proved
physical dilation isometry, with the original charge-one normalization. -/
def chargeTwoJetEvaluation (G : Geometry) (theta : Twist) (j : ℕ) (R : ℂ) :
    LLL G theta 2 →L[ℂ] ℂ :=
  (canonicalJetEvaluation (scaledGeometry G) (scaledTwist theta) j ((scale : ℂ)*R)).comp
    (scalingLinearIsometryEquiv G theta).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- The original periodized canonical jet transported by the same full
physical isometry, rather than a separately normalized evaluation vector. -/
def chargeTwoJetKernel (G : Geometry) (theta : Twist) (j : ℕ) (R : ℂ) : LLL G theta 2 :=
  scalingLinearIsometryEquiv G theta
    (rawPlaneJet (scaledGeometry G) (scaledTwist theta) j ((scale : ℂ)*R))

theorem chargeTwoJetKernel_reproduces (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) (f : LLL G theta 2) :
    inner ℂ (chargeTwoJetKernel G theta j R) f = chargeTwoJetEvaluation G theta j R f := by
  let e := scalingLinearIsometryEquiv G theta
  change inner ℂ (e _) f = _
  conv_lhs => rw [← e.apply_symm_apply f, e.inner_map_map]
  exact rawPlaneJet_inner_reproduces (scaledGeometry G) (scaledTwist theta) (e.symm f) j _

/-- Entire stripped factor in the scaled charge-one coordinates. -/
def chargeTwoScaledFactor (G : Geometry) (theta : Twist) (f : LLL G theta 2) : ℂ → ℂ :=
  canonicalRawStripped (scaledGeometry G) (scaledTwist theta)
    ((scalingLinearIsometryEquiv G theta).symm f)

theorem chargeTwoScaledFactor_differentiable (G : Geometry) (theta : Twist)
    (f : LLL G theta 2) : Differentiable ℂ (chargeTwoScaledFactor G theta f) :=
  canonicalRawStripped_differentiable _ _ _

theorem chargeTwoScaledFactor_factor (G : Geometry) (theta : Twist)
    (f : LLL G theta 2) (z : ℂ) :
    f.val z = gaussianFactor 2 z * chargeTwoScaledFactor G theta f ((scale : ℂ)*z) := by
  have h := canonicalRawStripped_factor (scaledGeometry G) (scaledTwist theta)
    ((scalingLinearIsometryEquiv G theta).symm f) ((scale : ℂ)*z)
  change f.val (((scale : ℂ)*z)/(scale : ℂ)) = _ at h
  have hs : (scale : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr scale_pos.ne'
  simpa only [mul_div_cancel_left₀ z hs, scaled_gaussian, chargeTwoScaledFactor] using h

/-- This centered entire factor retains the magnetic back-translation. -/
def chargeTwoCenteredFactor (G : Geometry) (theta : Twist) (f : LLL G theta 2)
    (R : ℂ) : ℂ → ℂ :=
  translatedStrippedFactor (-((scale : ℂ)*R)) (chargeTwoScaledFactor G theta f)

theorem chargeTwoCenteredFactor_differentiable (G : Geometry) (theta : Twist)
    (f : LLL G theta 2) (R : ℂ) : Differentiable ℂ (chargeTwoCenteredFactor G theta f R) :=
  translatedStrippedFactor_differentiable _ _ (chargeTwoScaledFactor_differentiable G theta f)

theorem chargeTwoJetEvaluation_eq_derivative (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) (f : LLL G theta 2) :
    chargeTwoJetEvaluation G theta j R f =
      iteratedDeriv j (chargeTwoCenteredFactor G theta f R) 0 /
        (Real.sqrt (j.factorial : ℝ) : ℂ) := rfl

/-- The product of the two actual centered factors cancels its magnetic
linear phases exactly in the relative Jacobi direction. -/
theorem chargeTwoCenteredFactor_pair (G : Geometry) (theta : Twist)
    (f g : LLL G theta 2) (R r : ℂ) :
    chargeTwoCenteredFactor G theta f R (((scale : ℂ)/2)*r) *
      chargeTwoCenteredFactor G theta g R (-((scale : ℂ)/2)*r) =
    correctedPairSlice G theta 2 2 (f ⊗ₜ[ℂ] g) R r := by
  unfold correctedPairSlice
  rw [rawPairFunction_tmul_apply, chargeTwoScaledFactor_factor, chargeTwoScaledFactor_factor]
  have hc := jacobi_covariant_gaussian_cancel 2 2 (by norm_num : (2:ℝ)+2 ≠ 0) R r
  norm_num only at hc
  have hj : jacobiFirst 2 2 R r = R+r/2 ∧ jacobiSecond 2 2 R r = R-r/2 := by
    constructor <;> norm_num [jacobiFirst, jacobiSecond] <;> ring
  have hright : Complex.exp ((relativeCharge 2 2 : ℂ)*(r*conj r)/2) *
      (gaussianFactor 2 (jacobiFirst 2 2 R r) * chargeTwoScaledFactor G theta f ((scale:ℂ)*jacobiFirst 2 2 R r) *
      (gaussianFactor 2 (jacobiSecond 2 2 R r) * chargeTwoScaledFactor G theta g ((scale:ℂ)*jacobiSecond 2 2 R r))) =
      gaussianFactor 4 R *
        (chargeTwoScaledFactor G theta f ((scale:ℂ)*(R+r/2)) *
          chargeTwoScaledFactor G theta g ((scale:ℂ)*(R-r/2))) := by
    calc
      _ = (Complex.exp ((relativeCharge 2 2 : ℂ)*(r*conj r)/2) *
        (gaussianFactor 2 (jacobiFirst 2 2 R r) * gaussianFactor 2 (jacobiSecond 2 2 R r))) *
        (chargeTwoScaledFactor G theta f ((scale:ℂ)*jacobiFirst 2 2 R r) *
        chargeTwoScaledFactor G theta g ((scale:ℂ)*jacobiSecond 2 2 R r)) := by ring
      _ = _ := by rw [hc, hj.1, hj.2]
  norm_num only [Nat.cast_ofNat, Prod.fst, Prod.snd]
  rw [hright]
  unfold chargeTwoCenteredFactor translatedStrippedFactor
  have harg₁ : (scale:ℂ)/2*r - -((scale:ℂ)*R) = (scale:ℂ)*(R+r/2) := by ring
  have harg₂ : -((scale:ℂ)/2)*r - -((scale:ℂ)*R) = (scale:ℂ)*(R-r/2) := by ring
  rw [harg₁, harg₂]
  calc
    _ = (Complex.exp (((scale:ℂ)/2*r) * conj (-((scale:ℂ)*R)) -
        (-((scale:ℂ)*R) * conj (-((scale:ℂ)*R))) / 2) *
      Complex.exp ((-((scale:ℂ)/2)*r) * conj (-((scale:ℂ)*R)) -
        (-((scale:ℂ)*R) * conj (-((scale:ℂ)*R))) / 2)) *
      (chargeTwoScaledFactor G theta f ((scale:ℂ)*(R+r/2)) *
        chargeTwoScaledFactor G theta g ((scale:ℂ)*(R-r/2))) := by ring
    _ = _ := by
      congr 1
      rw [← Complex.exp_add]
      unfold gaussianFactor
      congr 1
      simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.ofReal_ofNat]
      linear_combination -(R * conj R) * scale_complex_sq

end TorusLean.Shared.RelativeJetMap
