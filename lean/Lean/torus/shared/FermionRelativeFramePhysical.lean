import torus.shared.FermionRelativeFrameBound
import torus.shared.FermionRelativeFrameCoefficientsPaper
import torus.shared.FermionRelativeFrameJetsIntegral

/-! The literal paper C_d in the original charge-four measure obeys the
asymptotic relative-frame estimate against the true original four-body S4.
All physical sectors N+4 and all spectator coordinates are retained. -/
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
open scoped BigOperators

/-- Original paper C_d density, in its unchanged charge-four anchor measure. -/
theorem paperFourBodyJet_normSq_integrable (G : Geometry) (theta : Twist) (N d : ℕ)
    (x : Exterior (Fin (physicalQ G theta+1)) ((N+2)+2)) :
    Integrable (fun R => occupationNormSq (physicalQ G theta) (paperFourBodyJet G theta d R x))
      (cellMeasure G 4) := by
  simp_rw [← fourBodyJet_eq_paper]
  exact fourBodyJet_normSq_integrable G theta N d x

/-- Literal T4: original signed C_d, original mu4, and the full physical input.
D is relative degree, hence the manuscript truncation is D=22. -/
def physicalFourJetEnergy (G : Geometry) (theta : Twist) (N D : ℕ)
    (f : PhysicalFermion G theta ((N+2)+2)) : ℝ :=
  ∫ R, ∑ d : Fin (D+1), occupationNormSq (physicalQ G theta)
    (paperFourBodyJet G theta d.val R
      ((physicalExteriorEquiv G theta ((N+2)+2)).symm f : Space (physicalQ G theta)))
    ∂cellMeasure G 4

/-- Genuine Fubini and finite summation identify the tensor frame with paper
T4 exactly, with no factorial, area, or spectator-number adjustment. -/
theorem actualRelativeFourBodyForm_eq_physicalFourJetEnergy
    (G : Geometry) (theta : Twist) (N D : ℕ)
    (f : PhysicalFermion G theta ((N+2)+2)) :
    actualRelativeFourBodyForm G theta N D f = physicalFourJetEnergy G theta N D f := by
  classical
  let x := (physicalExteriorEquiv G theta ((N+2)+2)).symm f
  have hn (z : Configuration N) :
      ‖relativeJetTruncation G theta D (doublePairTensor G theta N x z)‖^2 =
      ∑ d : Fin (D+1), ∫ R, ‖(relativeJet G theta 2 2 d.val
        (doublePairTensor G theta N x z)).val R‖^2 ∂cellMeasure G 4 := by
    rw [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro d hd
    exact lll_norm_sq_eq_cellIntegral G theta 4
      (relativeJet G theta 2 2 d.val (doublePairTensor G theta N x z))
  change (∫ z, ‖relativeJetTruncation G theta D (doublePairTensor G theta N x z)‖^2
    ∂sectorMeasure G N) = ∫ R, ∑ d : Fin (D+1),
      occupationNormSq (physicalQ G theta) (paperFourBodyJet G theta d.val R x) ∂cellMeasure G 4
  calc
    _ = ∫ z, ∑ d : Fin (D+1), ∫ R, ‖(relativeJet G theta 2 2 d.val
        (doublePairTensor G theta N x z)).val R‖^2 ∂cellMeasure G 4 ∂sectorMeasure G N :=
      integral_congr_ae (Filter.Eventually.of_forall hn)
    _ = ∑ d : Fin (D+1), ∫ z, ∫ R, ‖(relativeJet G theta 2 2 d.val
        (doublePairTensor G theta N x z)).val R‖^2 ∂cellMeasure G 4 ∂sectorMeasure G N :=
      integral_finsetSum Finset.univ (fun d _ =>
        (relativeJet_doublePairTensor_integrable G theta N d.val x).integral_prod_left)
    _ = ∑ d : Fin (D+1), ∫ R, occupationNormSq (physicalQ G theta)
        (fourBodyJet G theta d.val R x) ∂cellMeasure G 4 := by
      apply Finset.sum_congr rfl
      intro d hd
      exact relativeJet_doublePairTensor_integral_swap G theta N d.val x
    _ = ∑ d : Fin (D+1), ∫ R, occupationNormSq (physicalQ G theta)
        (paperFourBodyJet G theta d.val R x) ∂cellMeasure G 4 := by
      simp_rw [fourBodyJet_eq_paper]
    _ = _ := (integral_finsetSum Finset.univ
      (fun d _ => paperFourBodyJet_normSq_integrable G theta N d.val x)).symm

/-- Unconditional true paper T4 bound at any fixed finite relative degree. -/
theorem physicalFourJetEnergy_exists_threshold (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (G : Geometry) (theta : Twist), L ≤ systole G →
      ∀ (N : ℕ) (f : PhysicalFermion G theta ((N+2)+2)),
        physicalFourJetEnergy G theta N D f ≤ (1+ε) *
          (occupationInner (physicalQ G theta)
            ((physicalExteriorEquiv G theta ((N+2)+2)).symm f : Space (physicalQ G theta))
            (matrixFourBody (physicalQ G theta) (contactMatrix G theta)
              ((physicalExteriorEquiv G theta ((N+2)+2)).symm f : Space (physicalQ G theta)))).re := by
  obtain ⟨L, hL1, hL⟩ := actualRelativeFourBody_exists_threshold D ε hε
  refine ⟨L, hL1, fun G theta hG N f => ?_⟩
  rw [← actualRelativeFourBodyForm_eq_physicalFourJetEnergy]
  exact hL G theta hG N f

/-- Paper C_0,...,C_22 are controlled by the same true S4 for every physical
sector N+4, at one shape-, twist-, and particle-number-independent threshold. -/
theorem physicalFourJetEnergy_degree22_exists_threshold (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (G : Geometry) (theta : Twist), L ≤ systole G →
      ∀ (N : ℕ) (f : PhysicalFermion G theta ((N+2)+2)),
        physicalFourJetEnergy G theta N 22 f ≤ (1+ε) *
          (occupationInner (physicalQ G theta)
            ((physicalExteriorEquiv G theta ((N+2)+2)).symm f : Space (physicalQ G theta))
            (matrixFourBody (physicalQ G theta) (contactMatrix G theta)
              ((physicalExteriorEquiv G theta ((N+2)+2)).symm f : Space (physicalQ G theta)))).re :=
  physicalFourJetEnergy_exists_threshold 22 ε hε

#print axioms paperFourBodyJet_normSq_integrable
#print axioms actualRelativeFourBodyForm_eq_physicalFourJetEnergy
#print axioms physicalFourJetEnergy_exists_threshold
#print axioms physicalFourJetEnergy_degree22_exists_threshold
end TorusLean.Shared.FermionRelativeFrame
