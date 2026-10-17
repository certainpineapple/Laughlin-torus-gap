import torus.shared.RelativeJetMapChargeTwo
import torus.shared.PlaneJetMixedPolynomial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.RelativeJetMap
open TorusLean.Geometry TorusLean.Shared.ChargeTwoScaling
open TorusLean.Shared.ChargeTwoIsometry TorusLean.Shared.PlaneJetMembership
open TorusLean.Shared.PlaneJetMixedPolynomial TorusLean.Shared.PlaneJetLaguerreGram
open scoped ComplexConjugate

/-- Both slots of the original magnetic cocycle scale to physical charge2. -/
theorem scaled_chargeTwo_cocycle (x y : ℂ) :
    magneticCocycle 1 ((scale:ℂ)*x) ((scale:ℂ)*y) = magneticCocycle 2 x y := by
  unfold magneticCocycle
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_one, Complex.ofReal_ofNat, one_mul]
  linear_combination -(x*conj y-conj x*y)/2 * scale_complex_sq

/-- Original-lattice image coefficient for the physical charge-two jets,
retaining both cocycles, the common inverse chi squared and all COM points. -/
def chargeTwoImageCoefficient (G : Geometry) (theta : Twist) (j m : ℕ)
    (R S : ℂ) (p : ℤ × ℤ) : ℂ :=
  (latticeChi G.M theta.theta1 theta.theta2 p ^ 2)⁻¹ *
    magneticCocycle 2 (latticePeriod G.omega1 G.omega2 p) S *
    magneticCocycle 2 (-R) (latticePeriod G.omega1 G.omega2 p + S) *
    mixedCoefficient j m ((scale:ℂ) * (latticePeriod G.omega1 G.omega2 p + S - R))

theorem chargeTwoImageCoefficient_eq_scaled (G : Geometry) (theta : Twist)
    (j m : ℕ) (R S : ℂ) (p : ℤ × ℤ) :
    chargeTwoImageCoefficient G theta j m R S p =
      imagePhase (scaledGeometry G) (scaledTwist theta) ((scale:ℂ)*R) ((scale:ℂ)*S) p *
        mixedCoefficient j m
          (imageDisplacement (scaledGeometry G) ((scale:ℂ)*R) ((scale:ℂ)*S) p) := by
  unfold chargeTwoImageCoefficient imagePhase imageDisplacement
  rw [scaled_period, scaled_character, ← mul_neg, ← mul_add,
    scaled_chargeTwo_cocycle, scaled_chargeTwo_cocycle]
  congr 2
  ring

/-- Exact single-image HasSum of the original physical charge-two canonical
Gram, derived by the previously proved full physical dilation isometry. -/
theorem chargeTwoJetKernel_gram_hasSum (G : Geometry) (theta : Twist)
    (j m : ℕ) (R S : ℂ) :
    HasSum (chargeTwoImageCoefficient G theta j m R S)
      (inner ℂ (chargeTwoJetKernel G theta j R) (chargeTwoJetKernel G theta m S)) := by
  have h := rawPlaneJet_mixed_gram_hasSum (scaledGeometry G) (scaledTwist theta)
    j m ((scale:ℂ)*R) ((scale:ℂ)*S)
  change HasSum (fun p => chargeTwoImageCoefficient G theta j m R S p) _
  simpa only [chargeTwoJetKernel, LinearIsometryEquiv.inner_map_map,
    lll_inner_eq_cellInner, rawPlaneJet_val, chargeTwoImageCoefficient_eq_scaled] using h

/-- Absolute norm summability follows from genuine unconditional complex
HasSum in finite dimension; no positivity or majorant assumption is added. -/
theorem chargeTwoJetKernel_gram_summable_norm (G : Geometry) (theta : Twist)
    (j m : ℕ) (R S : ℂ) :
    Summable (fun p : ℤ × ℤ => ‖chargeTwoImageCoefficient G theta j m R S p‖) :=
  (chargeTwoJetKernel_gram_hasSum G theta j m R S).summable.norm

theorem chargeTwoJetKernel_gram_tsum (G : Geometry) (theta : Twist)
    (j m : ℕ) (R S : ℂ) :
    inner ℂ (chargeTwoJetKernel G theta j R) (chargeTwoJetKernel G theta m S) =
      ∑' p : ℤ × ℤ, chargeTwoImageCoefficient G theta j m R S p :=
  (chargeTwoJetKernel_gram_hasSum G theta j m R S).tsum_eq.symm

end TorusLean.Shared.RelativeJetMap
