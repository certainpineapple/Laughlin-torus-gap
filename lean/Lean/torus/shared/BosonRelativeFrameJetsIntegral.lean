import torus.shared.BosonRelativeFrameJets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonRelativeFrame
open MeasureTheory TorusLean.Boson
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonContactForm TorusLean.Shared.RelativeJetMap
open scoped TensorProduct ComplexConjugate BigOperators

/-- Each fixed finite orbital-pair tensor has a genuine full charge-four
jet section, so its anchor cross-products have the original cell integrability. -/
def pairJetSection (G : Geometry) (theta : Twist) (d : ℕ)
    (a : PairIndex G theta × PairIndex G theta) : LLL G theta 4 :=
  relativeJet G theta 2 2 d (pairSection G theta a.1 ⊗ₜ[ℂ] pairSection G theta a.2)

theorem relativeJet_doublePairTensor_expansion (G : Geometry) (theta : Twist) (N d : ℕ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (z : Configuration N) (R : ℂ) :
    (relativeJet G theta 2 2 d (doublePairTensor G theta N p z)).val R =
      ∑ a : PairIndex G theta × PairIndex G theta,
        coreFunction G theta N (TwoBodyLift.pairRemove a.2 (TwoBodyLift.pairRemove a.1 p)) z *
          (pairJetSection G theta d a).val R := by
  change lllEvaluation G theta 4 R (relativeJet G theta 2 2 d (doublePairTensor G theta N p z)) = _
  simp only [doublePairTensor, map_sum, map_smul, smul_eq_mul, Fintype.sum_prod_type,
    pairJetSection, lllEvaluation_apply]

theorem pairJetSection_cross_integrable (G : Geometry) (theta : Twist) (N d : ℕ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (a b : PairIndex G theta × PairIndex G theta) :
    Integrable (fun x : Configuration N × ℂ =>
      conj (coreFunction G theta N (TwoBodyLift.pairRemove a.2 (TwoBodyLift.pairRemove a.1 p)) x.1 *
        (pairJetSection G theta d a).val x.2) *
      (coreFunction G theta N (TwoBodyLift.pairRemove b.2 (TwoBodyLift.pairRemove b.1 p)) x.1 *
        (pairJetSection G theta d b).val x.2))
      ((sectorMeasure G N).prod (cellMeasure G 4)) := by
  have hcore := coreFunction_cross_integrable G theta N
    (TwoBodyLift.pairRemove a.2 (TwoBodyLift.pairRemove a.1 p))
    (TwoBodyLift.pairRemove b.2 (TwoBodyLift.pairRemove b.1 p))
  have hcell := cellInner_integrable G 4 (pairJetSection G theta d a).val
    (pairJetSection G theta d b).val
    (rawLLL_continuous G theta 4 (pairJetSection G theta d a))
    (rawLLL_continuous G theta 4 (pairJetSection G theta d b))
  convert hcore.mul_prod hcell using 1
  funext x
  simp only [map_mul]
  ring

/-- Actual product-measure integrability of the jet density, established
from finite cross-products before interchanging the physical integrals. -/
theorem relativeJet_doublePairTensor_integrable (G : Geometry) (theta : Twist) (N d : ℕ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    Integrable (fun x : Configuration N × ℂ =>
      ‖(relativeJet G theta 2 2 d (doublePairTensor G theta N p x.1)).val x.2‖^2)
      ((sectorMeasure G N).prod (cellMeasure G 4)) := by
  have h : Integrable (fun x : Configuration N × ℂ =>
      conj ((relativeJet G theta 2 2 d (doublePairTensor G theta N p x.1)).val x.2) *
        (relativeJet G theta 2 2 d (doublePairTensor G theta N p x.1)).val x.2)
      ((sectorMeasure G N).prod (cellMeasure G 4)) := by
    simp_rw [relativeJet_doublePairTensor_expansion]
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
    apply integrable_finsetSum
    intro a _
    apply integrable_finsetSum
    intro b _
    exact pairJetSection_cross_integrable G theta N d p b a
  have hre := h.re
  change Integrable (fun x : Configuration N × ℂ =>
      (conj ((relativeJet G theta 2 2 d (doublePairTensor G theta N p x.1)).val x.2) *
        (relativeJet G theta 2 2 d (doublePairTensor G theta N p x.1)).val x.2).re)
      ((sectorMeasure G N).prod (cellMeasure G 4)) at hre
  simpa only [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re] using hre

/-- Fubini now converts the spectator-first genuine frame density into
the paper's original C_d occupation norm at each anchor. -/
theorem relativeJet_doublePairTensor_integral_swap (G : Geometry) (theta : Twist) (N d : ℕ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (hp : p.IsHomogeneous ((N+2)+2)) :
    (∫ z, ∫ R, ‖(relativeJet G theta 2 2 d (doublePairTensor G theta N p z)).val R‖^2
      ∂cellMeasure G 4 ∂sectorMeasure G N) =
      ∫ R, occupationMetricNormSq (fun _ => 1) (fourBodyJet G theta d R p) ∂cellMeasure G 4 := by
  rw [integral_integral_swap (relativeJet_doublePairTensor_integrable G theta N d p)]
  apply integral_congr_ae
  filter_upwards [] with R
  exact fourBodyJet_spectator_normSq G theta N d R p hp

end TorusLean.Shared.BosonRelativeFrame
