import torus.shared.FermionLocalJetFourCouplingSlaterListFastNormalize

/-! One exact original mode; all odd modes are reassembled in the original
forall theorem. This certificate computes derived lists, not supplied data. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

theorem sourceListCheckD10R03 :
    normalizeTermsFast (sourceTerms 10 10 3) =
      normalizeTermsFast (slaterTerms 10 3) := by
  simp only [sourceTerms,pairCoefficientList,coefficientList,slaterTerms,
    integerSlaterNumerator,OAI.Laughlin.Certificate.V,OAI.Laughlin.Certificate.U,
    Nat.choose_eq_fast_choose]
  decide +kernel

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceListCheckD10R03
