import torus.shared.FermionRelativeFrameCoefficientsPaper
import torus.shared.BosonAnchoredScalarExpansion
import torus.shared.BosonAnchoredCoefficientGrowth

/-! Rebuilt successfully with Lean 4.34.1 in the selected 3,177-module closure.
See [validation scope](../../../REBUILD.md) and ../../../REBUILD_VALIDATION.json.
The actual fermionic pair coherent generating function.
Only scalar Taylor convergence and the genuine charge-two section/scaling
interfaces are shared. No bosonic CCR or bosonic pair normalization is used.
The final HasSum is a complex occupation form on the actual whole Fock space;
no ambient norm is silently placed on the raw exterior carrier. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiPairGenerating
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalFermionNormalSquare
open TorusLean.Shared.FermionRelativeFrame TorusLean.Shared.RelativeJetMap
open TorusLean.Shared.ChargeTwoScaling TorusLean.Shared.ChargeTwoIsometry
open TorusLean.Shared.ChargeTwoEvaluation TorusLean.Shared.PlaneJetReproducing
open TorusLean.Shared.BosonAnchoredScalarExpansion
open TorusLean.Shared.BosonAnchoredCoefficientGrowth
open TorusLean.Shared.ThermalCoherentAnchoredSeries
open TorusLean.Fermion.LatticePacking
open scoped BigOperators ComplexConjugate

/-- The original charge-two coherent weight: no extra half or sqrt2 is
attached to the existing normalized pair descendant. -/
def pairWeight (z : ℂ) (p : ℕ) : ℂ :=
  gaussianFactor 2 z * ((scale : ℂ)*z)^p / (Real.sqrt (p.factorial:ℝ):ℂ)

/-- The inverse-scaled section pulls back to the original physical section. -/
private theorem scaled_section_pullback (G : Geometry) (theta : Twist)
    (f : LLL G theta 2) :
    (fun z => ((scalingLinearIsometryEquiv G theta).symm f).val ((scale:ℂ)*z)) =
      f.val := by
  funext z
  change f.val (((scale:ℂ)*z)/(scale:ℂ)) = f.val z
  have hs : (scale:ℂ)≠0 := Complex.ofReal_ne_zero.mpr scale_pos.ne'
  rw [mul_div_cancel_left₀ z hs]

/-- True charge-two scalar Taylor expansion, with the magnetic translation
retained. Its coefficients are the already defined physical evaluations. -/
theorem chargeTwo_coherent_hasSum (G : Geometry) (theta : Twist)
    (f : LLL G theta 2) (R z : ℂ) :
    HasSum (fun p : ℕ => pairWeight z p * chargeTwoJetEvaluation G theta p R f)
      (magneticTranslate 2 (-R) f.val z) := by
  have hs := primal_coherent_hasSum (scaledGeometry G) (scaledTwist theta)
    ((scalingLinearIsometryEquiv G theta).symm f) ((scale:ℂ)*R) ((scale:ℂ)*z)
  rw [show -((scale:ℂ)*R)=(scale:ℂ)*(-R) by ring,
    scaled_magneticTranslate, scaled_section_pullback] at hs
  convert hs using 1
  ext p
  simp only [pairWeight, primalCoherentWeight, scaled_gaussian]
  rfl

/-- This all-p bound is uniform in the original centre and retains the
actual charge-two cell norm. It is an analytic exchange bound, not a
same-H relative tail payment. -/
theorem chargeTwoJetEvaluation_norm_le (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (f : LLL G theta 2) (p : ℕ) (R : ℂ) :
    ‖chargeTwoJetEvaluation G theta p R f‖ ≤
      ((4096+gaussianConstant)*‖f‖)*((p:ℝ)+1) := by
  have hscaled : 1 ≤ systole (scaledGeometry G) :=
    scale_ge_one.trans (by simpa only [mul_one] using scaled_systole_lower G 1 hG)
  have hb := rawJetCoefficient_norm_le (scaledGeometry G) (scaledTwist theta)
    hscaled ((scalingLinearIsometryEquiv G theta).symm f) p ((scale:ℂ)*R)
  change ‖chargeTwoJetEvaluation G theta p R f‖ ≤ _ at hb
  simpa only [(scalingLinearIsometryEquiv G theta).symm.norm_map] using hb

/-- The actual physical coefficient discharges the polynomial premise used
by the existing absolute L1 anchored-series theorem. -/
theorem chargeTwoJetEvaluation_hasPolynomialNormBound
    (G : Geometry) (theta : Twist) (hG : 1 ≤ systole G)
    (f : LLL G theta 2) (R : ℂ) :
    HasPolynomialNormBound (fun p => chargeTwoJetEvaluation G theta p R f) := by
  refine ⟨(4096+gaussianConstant)*‖f‖,1,?_⟩
  intro p
  simpa only [pow_one] using chargeTwoJetEvaluation_norm_le G theta hG f p R

/-- The genuine whole-Fock pair generating function with an actual marked
annihilator and complex occupation cross form. The finite sum contains the
existing ordered pairSection=Wronksian/2 exactly once. This is the B_p used
by formalThreeSeed_image_mul_adjoint, not a newly defined effective source. -/
theorem pairAt_marked_cross_coherent_hasSum (G : Geometry) (theta : Twist)
    (k : ℕ) (R z : ℂ) (x y : Space (physicalQ G theta)) :
    HasSum (fun p : ℕ => pairWeight z p *
      occupationInner (physicalQ G theta) x
        (vectorAnnihilate (physicalQ G theta) (physicalJetCoordinates G theta k R)
          (pairDescendant G theta p R y)))
      (magneticTranslate 2 (-R)
        (fun S => occupationInner (physicalQ G theta) x
          (vectorAnnihilate (physicalQ G theta) (physicalJetCoordinates G theta k R)
            (pairAt G theta S y))) z) := by
  classical
  have hs := hasSum_sum
    (s := (Finset.univ : Finset (TorusLean.Shared.FermionRelativeFrame.PairIndex G theta)))
    (fun a _ => (chargeTwo_coherent_hasSum G theta (pairSection G theta a) R z).mul_right
      (occupationInner (physicalQ G theta) x
        (vectorAnnihilate (physicalQ G theta) (physicalJetCoordinates G theta k R)
          (modePairAnnihilate (physicalQ G theta) a y))))
  convert hs using 1
  · ext p
    simp only [pairDescendant, LinearMap.sum_apply, LinearMap.smul_apply,
      map_sum, map_smul, occupationInner_sum_right, occupationInner_smul_right,
      Finset.mul_sum, mul_assoc]
  · simp only [magneticTranslate, pairAt_section_expansion,
      LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
      occupationInner_sum_right, occupationInner_smul_right,
      Finset.mul_sum, mul_assoc]

/-- The p=0 coefficient is the original negative m=1 B_R. -/
theorem pairAt_marked_coherent_ground (G : Geometry) (theta : Twist)
    (k : ℕ) (R : ℂ) (x y : Space (physicalQ G theta)) :
    pairWeight 0 0 * occupationInner (physicalQ G theta) x
      (vectorAnnihilate (physicalQ G theta) (physicalJetCoordinates G theta k R)
        (pairDescendant G theta 0 R y)) =
      occupationInner (physicalQ G theta) x
        (vectorAnnihilate (physicalQ G theta) (physicalJetCoordinates G theta k R)
          (pairAt G theta R y)) := by
  simp [pairWeight, gaussianFactor, pairDescendant_zero]

end TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiPairGenerating
