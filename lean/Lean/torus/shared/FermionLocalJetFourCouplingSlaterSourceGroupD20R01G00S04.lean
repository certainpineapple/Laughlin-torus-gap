import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks

/-! Contiguous original p blocks, each original normalized block and
prefix merge checked independently in the kernel. Raw source literals are omitted;
normalization is computed directly from the unchanged original sourceBlock. The arbitrary literal
start becomes an actual source prefix only through the final fold proof. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

def sourceGroupStartD20R01G00S04 : List Term := []

def sourceGroupEndD20R01G00S04 : List Term := [
    ((1,3,8,9),243290200817664000),
    ((0,4,8,9),486580401635328000),
    ((1,3,7,10),729870602452992000),
    ((0,4,7,10),1459741204905984000),
    ((1,2,8,10),-243290200817664000),
    ((0,3,8,10),-729870602452992000),
    ((0,2,9,10),243290200817664000),
    ((1,3,6,11),1216451004088320000),
    ((0,4,6,11),2432902008176640000),
    ((1,2,7,11),-486580401635328000),
    ((0,3,7,11),-1459741204905984000),
    ((0,2,8,11),729870602452992000),
    ((0,1,9,11),-243290200817664000),
    ((1,3,5,12),1703031405723648000),
    ((0,4,5,12),3406062811447296000),
    ((1,2,6,12),-729870602452992000),
    ((0,3,6,12),-2189611807358976000),
    ((0,2,7,12),1216451004088320000),
    ((0,1,8,12),-486580401635328000),
    ((1,3,4,13),2189611807358976000),
    ((1,2,5,13),-973160803270656000),
    ((0,3,5,13),-2919482409811968000),
    ((0,2,6,13),1703031405723648000),
    ((0,1,7,13),-729870602452992000),
    ((1,2,4,14),-1216451004088320000),
    ((0,3,4,14),-9001737430253568000),
    ((0,2,5,14),2189611807358976000),
    ((0,1,6,14),-973160803270656000),
    ((1,2,3,15),-4622513815535616000),
    ((0,2,4,15),-3649353012264960000),
    ((0,1,5,15),-1216451004088320000),
    ((0,2,3,16),8271866827800576000),
    ((0,1,4,16),-8758447229435904000),
    ((0,1,3,17),8271866827800576000),
    ((0,1,2,18),-8271866827800576000)
  ]

private def normalP00 : List Term := [
    ((0,1,9,11),-243290200817664000),
    ((0,1,8,12),-486580401635328000),
    ((0,1,7,13),-729870602452992000),
    ((0,1,6,14),-973160803270656000),
    ((0,1,5,15),-1216451004088320000),
    ((0,1,4,16),-1459741204905984000),
    ((0,1,3,17),-1703031405723648000),
    ((0,1,2,18),-1946321606541312000)
  ]

private def accP01 : List Term := [
    ((0,1,9,11),-243290200817664000),
    ((0,1,8,12),-486580401635328000),
    ((0,1,7,13),-729870602452992000),
    ((0,1,6,14),-973160803270656000),
    ((0,1,5,15),-1216451004088320000),
    ((0,1,4,16),-1459741204905984000),
    ((0,1,3,17),-1703031405723648000),
    ((0,1,2,18),-1946321606541312000)
  ]

private theorem normalCheckP00 : normalizeTermsFast (sourceBlock 20 20 1 0)=normalP00 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP00 : mergeTerms sourceGroupStartD20R01G00S04 normalP00=accP01 := by
  decide +kernel

private def normalP01 : List Term := [
    ((0,2,9,10),243290200817664000),
    ((0,2,8,11),729870602452992000),
    ((0,2,7,12),1216451004088320000),
    ((0,2,6,13),1703031405723648000),
    ((0,2,5,14),2189611807358976000),
    ((0,2,4,15),2676192208994304000),
    ((0,2,3,16),3162772610629632000),
    ((0,1,2,18),-4135933413900288000)
  ]

private def accP02 : List Term := [
    ((0,2,9,10),243290200817664000),
    ((0,2,8,11),729870602452992000),
    ((0,1,9,11),-243290200817664000),
    ((0,2,7,12),1216451004088320000),
    ((0,1,8,12),-486580401635328000),
    ((0,2,6,13),1703031405723648000),
    ((0,1,7,13),-729870602452992000),
    ((0,2,5,14),2189611807358976000),
    ((0,1,6,14),-973160803270656000),
    ((0,2,4,15),2676192208994304000),
    ((0,1,5,15),-1216451004088320000),
    ((0,2,3,16),3162772610629632000),
    ((0,1,4,16),-1459741204905984000),
    ((0,1,3,17),-1703031405723648000),
    ((0,1,2,18),-6082255020441600000)
  ]

private theorem normalCheckP01 : normalizeTermsFast (sourceBlock 20 20 1 1)=normalP01 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP01 : mergeTerms accP01 normalP01=accP02 := by
  decide +kernel

private def normalP02 : List Term := [
    ((1,2,8,10),-243290200817664000),
    ((0,3,8,10),-729870602452992000),
    ((1,2,7,11),-486580401635328000),
    ((0,3,7,11),-1459741204905984000),
    ((1,2,6,12),-729870602452992000),
    ((0,3,6,12),-2189611807358976000),
    ((1,2,5,13),-973160803270656000),
    ((0,3,5,13),-2919482409811968000),
    ((1,2,4,14),-1216451004088320000),
    ((0,3,4,14),-3649353012264960000),
    ((1,2,3,15),-1459741204905984000),
    ((0,2,3,16),5109094217170944000),
    ((0,1,3,17),5838964819623936000),
    ((0,1,2,18),-2189611807358976000)
  ]

private def accP03 : List Term := [
    ((1,2,8,10),-243290200817664000),
    ((0,3,8,10),-729870602452992000),
    ((0,2,9,10),243290200817664000),
    ((1,2,7,11),-486580401635328000),
    ((0,3,7,11),-1459741204905984000),
    ((0,2,8,11),729870602452992000),
    ((0,1,9,11),-243290200817664000),
    ((1,2,6,12),-729870602452992000),
    ((0,3,6,12),-2189611807358976000),
    ((0,2,7,12),1216451004088320000),
    ((0,1,8,12),-486580401635328000),
    ((1,2,5,13),-973160803270656000),
    ((0,3,5,13),-2919482409811968000),
    ((0,2,6,13),1703031405723648000),
    ((0,1,7,13),-729870602452992000),
    ((1,2,4,14),-1216451004088320000),
    ((0,3,4,14),-3649353012264960000),
    ((0,2,5,14),2189611807358976000),
    ((0,1,6,14),-973160803270656000),
    ((1,2,3,15),-1459741204905984000),
    ((0,2,4,15),2676192208994304000),
    ((0,1,5,15),-1216451004088320000),
    ((0,2,3,16),8271866827800576000),
    ((0,1,4,16),-1459741204905984000),
    ((0,1,3,17),4135933413900288000),
    ((0,1,2,18),-8271866827800576000)
  ]

private theorem normalCheckP02 : normalizeTermsFast (sourceBlock 20 20 1 2)=normalP02 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP02 : mergeTerms accP02 normalP02=accP03 := by
  decide +kernel

private def normalP03 : List Term := [
    ((1,3,8,9),243290200817664000),
    ((0,4,8,9),486580401635328000),
    ((1,3,7,10),729870602452992000),
    ((0,4,7,10),1459741204905984000),
    ((1,3,6,11),1216451004088320000),
    ((0,4,6,11),2432902008176640000),
    ((1,3,5,12),1703031405723648000),
    ((0,4,5,12),3406062811447296000),
    ((1,3,4,13),2189611807358976000),
    ((0,3,4,14),-5352384417988608000),
    ((1,2,3,15),-3162772610629632000),
    ((0,2,4,15),-6325545221259264000),
    ((0,1,4,16),-7298706024529920000),
    ((0,1,3,17),4135933413900288000)
  ]

private theorem normalCheckP03 : normalizeTermsFast (sourceBlock 20 20 1 3)=normalP03 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP03 : mergeTerms accP03 normalP03=sourceGroupEndD20R01G00S04 := by
  decide +kernel

theorem sourceGroupCheckD20R01G00S04 :
    foldNormalBlocks sourceGroupStartD20R01G00S04
      [sourceBlock 20 20 1 0,sourceBlock 20 20 1 1,sourceBlock 20 20 1 2,sourceBlock 20 20 1 3]=sourceGroupEndD20R01G00S04 := by
  rw [foldNormalBlocks,normalCheckP00,mergeCheckP00]
  rw [foldNormalBlocks,normalCheckP01,mergeCheckP01]
  rw [foldNormalBlocks,normalCheckP02,mergeCheckP02]
  rw [foldNormalBlocks,normalCheckP03,mergeCheckP03]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceGroupCheckD20R01G00S04
