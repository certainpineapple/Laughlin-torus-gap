import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

/- Original degree-23 table identity isolated from the separate source identity. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalSlaterGramTableCheck23 :
    OAI.Laughlin.Certificate.gramRational 23 = TorusLean.FermionM3.gramTable23 := by
  decide +kernel

#print axioms originalSlaterGramTableCheck23
end TorusLean.Shared.FermionLocalJet.FourCoupling
