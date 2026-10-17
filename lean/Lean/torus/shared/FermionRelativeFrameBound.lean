import torus.shared.FermionRelativeFrameEnergy
import torus.shared.RelativeJetFrameAsymptotic

/-! Integrate the genuine uniform asymptotic frame bound over every physical
spectator. The right side is the previously defined true CAR matrixFourBody;
no spectral-gap, fixed numerical systole, or particle-number bound is asserted. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionRelativeFrame
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.PhysicalFermionCarrier TorusLean.Shared.PhysicalFermionExterior
open TorusLean.Shared.PhysicalFermionNormalSquare TorusLean.Shared.RelativeJetMap
open TorusLean.Fermion.LatticePacking
open scoped TensorProduct BigOperators

lemma tensorFunction_continuous (G : Geometry) (theta : Twist) (N : ℕ)
    (c : Word G theta N → ℂ) : Continuous (tensorFunction G theta N c) := by
  classical
  change Continuous (fun z => ∑ w, c w * wordFunction G theta N w z)
  apply continuous_finsetSum
  intro w hw
  exact continuous_const.mul (wordFunction_continuous G theta N w)

theorem physicalExteriorLinear_continuous (G : Geometry) (theta : Twist) (N : ℕ)
    (x : Exterior (Fin (physicalQ G theta+1)) N) :
    Continuous (physicalExteriorLinear G theta N x) := by
  change Continuous (physicalExteriorEquiv G theta N x).val
  rw [physicalExteriorEquiv_apply]
  exact tensorFunction_continuous G theta N _

theorem doublePairTensor_continuous (G : Geometry) (theta : Twist) (N : ℕ)
    (x : Exterior (Fin (physicalQ G theta+1)) ((N+2)+2)) :
    Continuous (doublePairTensor G theta N x) := by
  classical
  unfold doublePairTensor
  apply continuous_finsetSum
  intro a ha
  apply continuous_finsetSum
  intro b hb
  exact (physicalExteriorLinear_continuous G theta N _).smul
    (continuous_const : Continuous (fun _ : Configuration N =>
      pairSection G theta a ⊗ₜ[ℂ] pairSection G theta b))

/-- The genuine finite relative frame of the two original m=1 physical anchors. -/
def actualRelativeFourBodyForm (G : Geometry) (theta : Twist) (N D : ℕ)
    (f : PhysicalFermion G theta ((N+2)+2)) : ℝ :=
  ∫ z, ‖relativeJetTruncation G theta D (physicalDoublePairTensor G theta N f z)‖^2
    ∂sectorMeasure G N

/-- A general domination helper; the final theorem below supplies its frame
bound from the already proved, geometry-uniform asymptotic theorem. -/
theorem actualRelativeFourBody_integrable (G : Geometry) (theta : Twist) (N D : ℕ)
    (B : ℝ)
    (hframe : ∀ ψ : LLL G theta 2 ⊗[ℂ] LLL G theta 2,
      ‖relativeJetTruncation G theta D ψ‖^2 ≤ B * ‖ψ‖^2)
    (f : PhysicalFermion G theta ((N+2)+2)) :
    Integrable (fun z => ‖relativeJetTruncation G theta D
      (physicalDoublePairTensor G theta N f z)‖^2) (sectorMeasure G N) := by
  let x := (physicalExteriorEquiv G theta ((N+2)+2)).symm f
  have hc : Continuous (physicalDoublePairTensor G theta N f) :=
    doublePairTensor_continuous G theta N x
  have hj : Continuous (fun z => ‖relativeJetTruncation G theta D
      (physicalDoublePairTensor G theta N f z)‖^2) :=
    (((relativeJetTruncation G theta D).continuous.comp hc).norm).pow 2
  have hi := (doublePairTensor_normSq_integrable G theta N x).const_mul B
  apply hi.mono' hj.aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hframe _

/-- The original S4 pays the full physical spectator-frame cost. -/
theorem actualRelativeFourBody_le_S4 (G : Geometry) (theta : Twist) (N D : ℕ)
    (B : ℝ)
    (hframe : ∀ ψ : LLL G theta 2 ⊗[ℂ] LLL G theta 2,
      ‖relativeJetTruncation G theta D ψ‖^2 ≤ B * ‖ψ‖^2)
    (f : PhysicalFermion G theta ((N+2)+2)) :
    actualRelativeFourBodyForm G theta N D f ≤ B *
      (occupationInner (physicalQ G theta)
        ((physicalExteriorEquiv G theta ((N+2)+2)).symm f : Space (physicalQ G theta))
        (matrixFourBody (physicalQ G theta) (contactMatrix G theta)
          ((physicalExteriorEquiv G theta ((N+2)+2)).symm f : Space (physicalQ G theta)))).re := by
  let x := (physicalExteriorEquiv G theta ((N+2)+2)).symm f
  unfold actualRelativeFourBodyForm
  calc
    _ ≤ ∫ z, B * ‖physicalDoublePairTensor G theta N f z‖^2 ∂sectorMeasure G N :=
      integral_mono (actualRelativeFourBody_integrable G theta N D B hframe f)
        ((doublePairTensor_normSq_integrable G theta N x).const_mul B) (fun z => hframe _)
    _ = _ := by rw [integral_const_mul, physicalDoublePairTensor_integrated_normSq]

/-- At every fixed D, one threshold works for all geometries, twists,
particle numbers and full physical states. No frame-bound premise remains. -/
theorem actualRelativeFourBody_exists_threshold (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (G : Geometry) (theta : Twist), L ≤ systole G →
      ∀ (N : ℕ) (f : PhysicalFermion G theta ((N+2)+2)),
        actualRelativeFourBodyForm G theta N D f ≤ (1+ε) *
          (occupationInner (physicalQ G theta)
            ((physicalExteriorEquiv G theta ((N+2)+2)).symm f : Space (physicalQ G theta))
            (matrixFourBody (physicalQ G theta) (contactMatrix G theta)
              ((physicalExteriorEquiv G theta ((N+2)+2)).symm f : Space (physicalQ G theta)))).re := by
  obtain ⟨L, hL1, hL⟩ :=
    RelativeJetFrameAsymptotic.relativeJetTruncation_exists_threshold D ε hε
  refine ⟨L, hL1, fun G theta hG N f => ?_⟩
  exact actualRelativeFourBody_le_S4 G theta N D (1+ε) (hL G theta hG).2 f

#print axioms physicalExteriorLinear_continuous
#print axioms doublePairTensor_continuous
#print axioms actualRelativeFourBody_integrable
#print axioms actualRelativeFourBody_le_S4
#print axioms actualRelativeFourBody_exists_threshold
end TorusLean.Shared.FermionRelativeFrame
