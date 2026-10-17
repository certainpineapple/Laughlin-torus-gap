import torus.shared.FermionLocalJetFourCouplingOriginalQuadruples22
import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

/- Exact original Z table identity; source identity is a separate module. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalSlaterGramTableCheck22 :
    OAI.Laughlin.Certificate.gramRational 22 = TorusLean.FermionM3.gramTable22 := by
  unfold OAI.Laughlin.Certificate.gramRational OAI.Laughlin.Certificate.Z
  rw [ZEntrySplitCandidate.originalQuadruples22_exact]
  change @Eq (Matrix (Fin 11) (Fin 11) ℚ) _ _
  apply @of_decide_eq_true _ (Matrix.decidableEq _ _)
  decide +kernel

#print axioms originalSlaterGramTableCheck22
end TorusLean.Shared.FermionLocalJet.FourCoupling
