import torus.shared.BosonRelativeFrameBound
import torus.shared.BosonRelativeFrameJetsIntegral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonRelativeFrame
open MeasureTheory TorusLean.Boson
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonMembership
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonS4
open TorusLean.Shared.RelativeJetMap TorusLean.Shared.BosonSystole20Scalar
open TorusLean.Fermion.LatticePacking
open scoped BigOperators

/-- The original four-particle C_d output density is genuinely integrable
in the original charge-four anchor measure. -/
theorem fourBodyJet_normSq_integrable (G : Geometry) (theta : Twist) (N d : ℕ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (hp : p.IsHomogeneous ((N+2)+2)) :
    Integrable (fun R => occupationMetricNormSq (fun _ => 1) (fourBodyJet G theta d R p))
      (cellMeasure G 4) := by
  have h := (relativeJet_doublePairTensor_integrable G theta N d p).integral_prod_right
  simpa only [fourBodyJet_spectator_normSq G theta N d _ p hp] using h

/-- Paper T4 with the original signed C_d finite oscillator contraction,
original mu4 measure, and the original full physical input coordinates. -/
def physicalFourJetEnergy (G : Geometry) (theta : Twist) (N D : ℕ)
    (f : PhysicalBosonCarrier G theta ((N+2)+2)) : ℝ :=
  ∫ R, ∑ d : Fin (D+1), occupationMetricNormSq (fun _ => 1)
    (fourBodyJet G theta d.val R ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val)
    ∂cellMeasure G 4

/-- Genuine Fubini and finite sums identify the spectator-first frame
with the original physical T4 anchor integral, without extra normalization. -/
theorem actualRelativeFourBodyForm_eq_physicalFourJetEnergy
    (G : Geometry) (theta : Twist) (N D : ℕ)
    (f : PhysicalBosonCarrier G theta ((N+2)+2)) :
    actualRelativeFourBodyForm G theta N D f = physicalFourJetEnergy G theta N D f := by
  let p := ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val
  have hp : p.IsHomogeneous ((N+2)+2) :=
    ((physicalSectorEquiv G theta ((N+2)+2)).symm f).property
  have hn (z : Configuration N) :
      ‖relativeJetTruncation G theta D (doublePairTensor G theta N p z)‖^2 =
      ∑ d : Fin (D+1), ∫ R, ‖(relativeJet G theta 2 2 d.val
        (doublePairTensor G theta N p z)).val R‖^2 ∂cellMeasure G 4 := by
    rw [PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro d hd
    exact lll_norm_sq_eq_cellIntegral G theta 4
      (relativeJet G theta 2 2 d.val (doublePairTensor G theta N p z))
  change (∫ z, ‖relativeJetTruncation G theta D (doublePairTensor G theta N p z)‖^2
    ∂sectorMeasure G N) = ∫ R, ∑ d : Fin (D+1),
      occupationMetricNormSq (fun _ => 1) (fourBodyJet G theta d.val R p) ∂cellMeasure G 4
  calc
    _ = ∫ z, ∑ d : Fin (D+1), ∫ R, ‖(relativeJet G theta 2 2 d.val
        (doublePairTensor G theta N p z)).val R‖^2 ∂cellMeasure G 4 ∂sectorMeasure G N :=
      integral_congr_ae (Filter.Eventually.of_forall hn)
    _ = ∑ d : Fin (D+1), ∫ z, ∫ R, ‖(relativeJet G theta 2 2 d.val
        (doublePairTensor G theta N p z)).val R‖^2 ∂cellMeasure G 4 ∂sectorMeasure G N :=
      integral_finsetSum Finset.univ (fun d _ =>
        (relativeJet_doublePairTensor_integrable G theta N d.val p).integral_prod_left)
    _ = ∑ d : Fin (D+1), ∫ R, occupationMetricNormSq (fun _ => 1)
        (fourBodyJet G theta d.val R p) ∂cellMeasure G 4 := by
      apply Finset.sum_congr rfl
      intro d hd
      exact relativeJet_doublePairTensor_integral_swap G theta N d.val p hp
    _ = _ := (integral_finsetSum Finset.univ
      (fun d _ => fourBodyJet_normSq_integrable G theta N d.val p hp)).symm

/-- The paper's actual four-particle relative-frame term is paid by the
same S4 term in the exact physical H square, uniformly in particle number. -/
theorem physicalFourJetEnergy_le_S4 (G : Geometry) (theta : Twist) (N D : ℕ)
    (hD : D ≤ 16) (hL : 20 ≤ systole G)
    (f : PhysicalBosonCarrier G theta ((N+2)+2)) :
    physicalFourJetEnergy G theta N D f ≤
      (1+allowance) * actualPositiveFourBodyForm G theta N f := by
  rw [← actualRelativeFourBodyForm_eq_physicalFourJetEnergy]
  exact actualRelativeFourBody_le_S4 G theta N D hD hL f

#print axioms fourBodyJet_normSq_integrable
#print axioms actualRelativeFourBodyForm_eq_physicalFourJetEnergy
#print axioms physicalFourJetEnergy_le_S4
end TorusLean.Shared.BosonRelativeFrame
