import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks

/-! Exact composition of certified contiguous source blocks. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

theorem foldNormalBlocks_append (acc : List Term) (bs cs : List (List Term)) :
    foldNormalBlocks acc (bs++cs)=foldNormalBlocks (foldNormalBlocks acc bs) cs := by
  induction bs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.cons_append,foldNormalBlocks,ih]

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.foldNormalBlocks_append
