import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks

/-! Contiguous original p blocks, each original normalized block and
prefix merge checked independently in the kernel. Raw source literals are omitted;
normalization is computed directly from the unchanged original sourceBlock. The arbitrary literal
start becomes an actual source prefix only through the final fold proof. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

def sourceGroupStartD22R01G05S04 : List Term := [
    ((0,2,10,11),102181884343418880000),
    ((0,2,9,12),306545653030256640000),
    ((0,1,10,12),-102181884343418880000),
    ((0,2,8,13),510909421717094400000),
    ((0,1,9,13),-204363768686837760000),
    ((0,2,7,14),715273190403932160000),
    ((0,1,8,14),-306545653030256640000),
    ((0,2,6,15),919636959090769920000),
    ((0,1,7,15),-408727537373675520000),
    ((0,2,5,16),1124000727777607680000),
    ((0,1,6,16),-510909421717094400000),
    ((0,2,4,17),1328364496464445440000),
    ((0,1,5,17),-613091306060513280000),
    ((0,2,3,18),1532728265151283200000),
    ((0,1,4,18),-715273190403932160000),
    ((0,1,3,19),-817455074747351040000),
    ((0,1,2,20),-2861092761615728640000)
  ]

def sourceGroupEndD22R01G05S04 : List Term := []

private def normalP20 : List Term := [
    ((0,2,10,11),-102181884343418880000),
    ((0,2,9,12),-306545653030256640000),
    ((0,2,8,13),-510909421717094400000),
    ((0,2,7,14),-715273190403932160000),
    ((0,2,6,15),-919636959090769920000),
    ((0,2,5,16),-1124000727777607680000),
    ((0,2,4,17),-1328364496464445440000),
    ((0,2,3,18),-1532728265151283200000),
    ((0,1,2,20),1941455802524958720000)
  ]

private def accP21 : List Term := [
    ((0,1,10,12),-102181884343418880000),
    ((0,1,9,13),-204363768686837760000),
    ((0,1,8,14),-306545653030256640000),
    ((0,1,7,15),-408727537373675520000),
    ((0,1,6,16),-510909421717094400000),
    ((0,1,5,17),-613091306060513280000),
    ((0,1,4,18),-715273190403932160000),
    ((0,1,3,19),-817455074747351040000),
    ((0,1,2,20),-919636959090769920000)
  ]

private theorem normalCheckP20 : normalizeTermsFast (sourceBlock 22 22 1 20)=normalP20 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP20 : mergeTerms sourceGroupStartD22R01G05S04 normalP20=accP21 := by
  decide +kernel

private def normalP21 : List Term := [
    ((0,1,10,12),102181884343418880000),
    ((0,1,9,13),204363768686837760000),
    ((0,1,8,14),306545653030256640000),
    ((0,1,7,15),408727537373675520000),
    ((0,1,6,16),510909421717094400000),
    ((0,1,5,17),613091306060513280000),
    ((0,1,4,18),715273190403932160000),
    ((0,1,3,19),817455074747351040000),
    ((0,1,2,20),919636959090769920000)
  ]

private def accP22 : List Term := []

private theorem normalCheckP21 : normalizeTermsFast (sourceBlock 22 22 1 21)=normalP21 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP21 : mergeTerms accP21 normalP21=accP22 := by
  decide +kernel

private def normalP22 : List Term := []

private theorem normalCheckP22 : normalizeTermsFast (sourceBlock 22 22 1 22)=normalP22 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP22 : mergeTerms accP22 normalP22=sourceGroupEndD22R01G05S04 := by
  decide +kernel

theorem sourceGroupCheckD22R01G05S04 :
    foldNormalBlocks sourceGroupStartD22R01G05S04
      [sourceBlock 22 22 1 20,sourceBlock 22 22 1 21,sourceBlock 22 22 1 22]=sourceGroupEndD22R01G05S04 := by
  rw [foldNormalBlocks,normalCheckP20,mergeCheckP20]
  rw [foldNormalBlocks,normalCheckP21,mergeCheckP21]
  rw [foldNormalBlocks,normalCheckP22,mergeCheckP22]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceGroupCheckD22R01G05S04
