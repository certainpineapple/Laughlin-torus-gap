import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

/- Exact original Z table identity; source identity is a separate module. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalSlaterGramTableCheck06 :
    OAI.Laughlin.Certificate.gramRational 6 = TorusLean.FermionM3.gramTable06 := by
  decide +kernel

#print axioms originalSlaterGramTableCheck06
end TorusLean.Shared.FermionLocalJet.FourCoupling
