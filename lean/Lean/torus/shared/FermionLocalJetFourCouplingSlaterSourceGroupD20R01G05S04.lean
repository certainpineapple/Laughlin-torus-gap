import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks

/-! Contiguous original p blocks, each original normalized block and
prefix merge checked independently in the kernel. Raw source literals are omitted;
normalization is computed directly from the unchanged original sourceBlock. The arbitrary literal
start becomes an actual source prefix only through the final fold proof. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

def sourceGroupStartD20R01G05S04 : List Term := []

def sourceGroupEndD20R01G05S04 : List Term := []

private def normalP20 : List Term := []

private theorem normalCheckP20 : normalizeTermsFast (sourceBlock 20 20 1 20)=normalP20 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP20 : mergeTerms sourceGroupStartD20R01G05S04 normalP20=sourceGroupEndD20R01G05S04 := by
  decide +kernel

theorem sourceGroupCheckD20R01G05S04 :
    foldNormalBlocks sourceGroupStartD20R01G05S04
      [sourceBlock 20 20 1 20]=sourceGroupEndD20R01G05S04 := by
  rw [foldNormalBlocks,normalCheckP20,mergeCheckP20]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceGroupCheckD20R01G05S04
