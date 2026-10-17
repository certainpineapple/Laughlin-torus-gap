import torus.shared.CellTranslation
import torus.shared.CellHilbert

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FractionalTranslationIsometry
open TorusLean.Geometry
open TorusLean.Shared.CellTranslation TorusLean.Shared.MagneticCellUnfolding

def fractionalDisplacement (G : Geometry) (k a : ℕ) (q : ℤ × ℤ) : ℂ :=
  (((a : ℝ)/(k : ℝ) : ℝ) : ℂ) * latticePeriod G.omega1 G.omega2 q

def fractionalTranslateLinear (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (a : ℕ) (q : ℤ × ℤ) : LLL G theta k →ₗ[ℂ] LLL G theta k where
  toFun f := rawLLLFractionalTranslate G.M a k (Nat.pos_of_ne_zero (NeZero.ne k))
    G.omega1 G.omega2 G.area theta.theta1 theta.theta2 q f
  map_add' f g := by
    apply Subtype.ext
    funext z
    change magneticTranslate (k : ℝ) (fractionalDisplacement G k a q) (f.val+g.val) z = _
    simp only [magneticTranslate, Pi.add_apply, mul_add]
    rfl
  map_smul' c f := by
    apply Subtype.ext
    funext z
    change Complex.exp (magneticExponent (k : ℝ) z (fractionalDisplacement G k a q)) *
      (c * f.val (z-fractionalDisplacement G k a q)) =
      c * (Complex.exp (magneticExponent (k : ℝ) z (fractionalDisplacement G k a q)) *
        f.val (z-fractionalDisplacement G k a q))
    ring

theorem fractionalTranslateLinear_apply (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (a : ℕ) (q : ℤ × ℤ) (f : LLL G theta k) :
    (fractionalTranslateLinear G theta k a q f).val =
      magneticTranslate (k : ℝ) (fractionalDisplacement G k a q) f.val := rfl

theorem fractionalTranslateLinear_norm (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (a : ℕ) (q : ℤ × ℤ) (f : LLL G theta k) :
    ‖fractionalTranslateLinear G theta k a q f‖ = ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [lll_norm_sq_eq_cellIntegral, lll_norm_sq_eq_cellIntegral, fractionalTranslateLinear_apply]
  simp_rw [magneticTranslate_norm, sub_eq_add_neg]
  apply periodic_cellIntegral_translate G k (fun z => ‖f.val z‖^2)
  intro p z
  rw [add_comm]
  exact congrArg (fun r : ℝ => r^2)
    (rawLLL_norm_add_period G theta k ⟨f.val,f.property⟩ p z)

theorem fractionalDisplacement_neg (G : Geometry) (k a : ℕ) (q : ℤ × ℤ) :
    fractionalDisplacement G k a (-q) = -fractionalDisplacement G k a q := by
  simp only [fractionalDisplacement, latticePeriod_neg, mul_neg]

theorem fractionalTranslateLinear_inverse (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (a : ℕ) (q : ℤ × ℤ) (f : LLL G theta k) :
    fractionalTranslateLinear G theta k a q (fractionalTranslateLinear G theta k a (-q) f) = f := by
  apply Subtype.ext
  simp only [fractionalTranslateLinear_apply, fractionalDisplacement_neg]
  exact magneticTranslate_inverse _ _ _

/-- Genuine cell-Hilbert unitary for every integer-flux fractional period.
The full original carrier and twist are preserved, with no finite-mode cut. -/
def fractionalTranslationIsometry (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (a : ℕ) (q : ℤ × ℤ) : LLL G theta k ≃ₗᵢ[ℂ] LLL G theta k where
  toLinearEquiv := LinearEquiv.ofBijective (fractionalTranslateLinear G theta k a q) (by
    constructor
    · apply Function.LeftInverse.injective (g := fractionalTranslateLinear G theta k a (-q))
      intro f
      have h := fractionalTranslateLinear_inverse G theta k a (-q) f
      simpa only [neg_neg] using h
    · apply Function.RightInverse.surjective (g := fractionalTranslateLinear G theta k a (-q))
      exact fractionalTranslateLinear_inverse G theta k a q)

  norm_map' := fractionalTranslateLinear_norm G theta k a q

theorem fractionalTranslationIsometry_apply (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (a : ℕ) (q : ℤ × ℤ) (f : LLL G theta k) :
    (fractionalTranslationIsometry G theta k a q f).val =
      magneticTranslate (k : ℝ) (fractionalDisplacement G k a q) f.val := rfl

theorem fractionalTranslation_opNorm_le (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (a : ℕ) (q : ℤ × ℤ) :
    ‖(fractionalTranslationIsometry G theta k a q).toLinearIsometry.toContinuousLinearMap‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  change ‖fractionalTranslationIsometry G theta k a q f‖ ≤ 1 * ‖f‖
  rw [(fractionalTranslationIsometry G theta k a q).norm_map, one_mul]

#print axioms fractionalTranslateLinear_apply
#print axioms fractionalTranslateLinear_norm
#print axioms fractionalDisplacement_neg
#print axioms fractionalTranslateLinear_inverse
#print axioms fractionalTranslationIsometry_apply
#print axioms fractionalTranslation_opNorm_le
end TorusLean.Shared.FractionalTranslationIsometry
