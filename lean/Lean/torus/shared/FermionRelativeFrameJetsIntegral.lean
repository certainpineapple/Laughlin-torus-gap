import torus.shared.FermionRelativeFrameEnergy
import torus.shared.FermionRelativeFrameJets

/-! Actual product-measure integrability and Fubini for the original
fermionic spectator tensor's finite relative jets. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionRelativeFrame
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.PhysicalFermionExterior TorusLean.Shared.RelativeJetMap
open scoped TensorProduct ComplexConjugate BigOperators

def pairJetSection (G : Geometry) (theta : Twist) (d : ℕ)
    (a : PairIndex G theta × PairIndex G theta) : LLL G theta 4 :=
  relativeJet G theta 2 2 d (pairSection G theta a.1 ⊗ₜ[ℂ] pairSection G theta a.2)

theorem relativeJet_doublePairTensor_expansion (G : Geometry) (theta : Twist) (N d : ℕ)
    (x : Exterior (Fin (physicalQ G theta+1)) ((N+2)+2)) (z : Configuration N) (R : ℂ) :
    (relativeJet G theta 2 2 d (doublePairTensor G theta N x z)).val R =
      ∑ a : PairIndex G theta × PairIndex G theta,
        doubleSpectator G theta N x a.1 a.2 z * (pairJetSection G theta d a).val R := by
  change lllEvaluation G theta 4 R (relativeJet G theta 2 2 d (doublePairTensor G theta N x z)) = _
  simp only [doublePairTensor, map_sum, map_smul, smul_eq_mul, Fintype.sum_prod_type,
    pairJetSection, lllEvaluation_apply]

lemma pairJetSection_cross_integrable (G : Geometry) (theta : Twist) (N d : ℕ)
    (x : Exterior (Fin (physicalQ G theta+1)) ((N+2)+2))
    (a b : PairIndex G theta × PairIndex G theta) :
    Integrable (fun z : Configuration N × ℂ =>
      conj (doubleSpectator G theta N x a.1 a.2 z.1 * (pairJetSection G theta d a).val z.2) *
        (doubleSpectator G theta N x b.1 b.2 z.1 * (pairJetSection G theta d b).val z.2))
      ((sectorMeasure G N).prod (cellMeasure G 4)) := by
  have hsp := physicalExteriorLinear_cross_integrable G theta N
    (exteriorModePair G theta N a.2 (exteriorModePair G theta (N+2) a.1 x))
    (exteriorModePair G theta N b.2 (exteriorModePair G theta (N+2) b.1 x))
  have hc := cellInner_integrable G 4 (pairJetSection G theta d a).val (pairJetSection G theta d b).val
    (rawLLL_continuous G theta 4 (pairJetSection G theta d a))
    (rawLLL_continuous G theta 4 (pairJetSection G theta d b))
  convert hsp.mul_prod hc using 1
  funext z
  simp only [doubleSpectator, map_mul]
  ring

/-- Joint integrability is proved before any change of integration order. -/
theorem relativeJet_doublePairTensor_integrable (G : Geometry) (theta : Twist) (N d : ℕ)
    (x : Exterior (Fin (physicalQ G theta+1)) ((N+2)+2)) :
    Integrable (fun z : Configuration N × ℂ =>
      ‖(relativeJet G theta 2 2 d (doublePairTensor G theta N x z.1)).val z.2‖^2)
      ((sectorMeasure G N).prod (cellMeasure G 4)) := by
  have h : Integrable (fun z : Configuration N × ℂ =>
      conj ((relativeJet G theta 2 2 d (doublePairTensor G theta N x z.1)).val z.2) *
        (relativeJet G theta 2 2 d (doublePairTensor G theta N x z.1)).val z.2)
      ((sectorMeasure G N).prod (cellMeasure G 4)) := by
    simp_rw [relativeJet_doublePairTensor_expansion]
    simp only [map_sum, Finset.sum_mul, Finset.mul_sum]
    exact integrable_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ =>
      pairJetSection_cross_integrable G theta N d x b a))
  have hre := h.re
  change Integrable (fun z : Configuration N × ℂ =>
    (conj ((relativeJet G theta 2 2 d (doublePairTensor G theta N x z.1)).val z.2) *
      (relativeJet G theta 2 2 d (doublePairTensor G theta N x z.1)).val z.2).re) _ at hre
  simpa only [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re] using hre

theorem relativeJet_doublePairTensor_integral_swap (G : Geometry) (theta : Twist) (N d : ℕ)
    (x : Exterior (Fin (physicalQ G theta+1)) ((N+2)+2)) :
    (∫ z, ∫ R, ‖(relativeJet G theta 2 2 d (doublePairTensor G theta N x z)).val R‖^2
      ∂cellMeasure G 4 ∂sectorMeasure G N) =
      ∫ R, occupationNormSq (physicalQ G theta) (fourBodyJet G theta d R x) ∂cellMeasure G 4 := by
  rw [integral_integral_swap (relativeJet_doublePairTensor_integrable G theta N d x)]
  apply integral_congr_ae
  filter_upwards [] with R
  exact fourBodyJet_spectator_normSq G theta N d R x

theorem fourBodyJet_normSq_integrable (G : Geometry) (theta : Twist) (N d : ℕ)
    (x : Exterior (Fin (physicalQ G theta+1)) ((N+2)+2)) :
    Integrable (fun R => occupationNormSq (physicalQ G theta) (fourBodyJet G theta d R x))
      (cellMeasure G 4) := by
  have h := (relativeJet_doublePairTensor_integrable G theta N d x).integral_prod_right
  simpa only [fourBodyJet_spectator_normSq G theta N d _ x] using h

#print axioms relativeJet_doublePairTensor_integrable
#print axioms relativeJet_doublePairTensor_integral_swap
#print axioms fourBodyJet_normSq_integrable
end TorusLean.Shared.FermionRelativeFrame
