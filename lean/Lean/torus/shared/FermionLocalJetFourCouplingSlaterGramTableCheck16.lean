import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

/- Exact original Z table identity; source identity is a separate module. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalSlaterGramTableCheck16 :
    OAI.Laughlin.Certificate.gramRational 16 = TorusLean.FermionM3.gramTable16 := by
  decide +kernel

#print axioms originalSlaterGramTableCheck16
end TorusLean.Shared.FermionLocalJet.FourCoupling
