import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks

/-! Contiguous original p blocks, each original normalized block and
prefix merge checked independently in the kernel. Raw source literals are omitted;
normalization is computed directly from the unchanged original sourceBlock. The arbitrary literal
start becomes an actual source prefix only through the final fold proof. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

def sourceGroupStartD20R01G04S04 : List Term := [
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

def sourceGroupEndD20R01G04S04 : List Term := []

private def normalP16 : List Term := [
    ((1,3,8,9),-243290200817664000),
    ((0,4,8,9),-486580401635328000),
    ((1,3,7,10),-729870602452992000),
    ((0,4,7,10),-1459741204905984000),
    ((1,3,6,11),-1216451004088320000),
    ((0,4,6,11),-2432902008176640000),
    ((1,3,5,12),-1703031405723648000),
    ((0,4,5,12),-3406062811447296000),
    ((1,3,4,13),-2189611807358976000),
    ((0,3,4,14),5352384417988608000),
    ((1,2,3,15),3162772610629632000),
    ((0,2,4,15),6325545221259264000),
    ((0,1,4,16),7298706024529920000),
    ((0,1,3,17),-4135933413900288000)
  ]

private def accP17 : List Term := [
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

private theorem normalCheckP16 : normalizeTermsFast (sourceBlock 20 20 1 16)=normalP16 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP16 : mergeTerms sourceGroupStartD20R01G04S04 normalP16=accP17 := by
  decide +kernel

private def normalP17 : List Term := [
    ((1,2,8,10),243290200817664000),
    ((0,3,8,10),729870602452992000),
    ((1,2,7,11),486580401635328000),
    ((0,3,7,11),1459741204905984000),
    ((1,2,6,12),729870602452992000),
    ((0,3,6,12),2189611807358976000),
    ((1,2,5,13),973160803270656000),
    ((0,3,5,13),2919482409811968000),
    ((1,2,4,14),1216451004088320000),
    ((0,3,4,14),3649353012264960000),
    ((1,2,3,15),1459741204905984000),
    ((0,2,3,16),-5109094217170944000),
    ((0,1,3,17),-5838964819623936000),
    ((0,1,2,18),2189611807358976000)
  ]

private def accP18 : List Term := [
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

private theorem normalCheckP17 : normalizeTermsFast (sourceBlock 20 20 1 17)=normalP17 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP17 : mergeTerms accP17 normalP17=accP18 := by
  decide +kernel

private def normalP18 : List Term := [
    ((0,2,9,10),-243290200817664000),
    ((0,2,8,11),-729870602452992000),
    ((0,2,7,12),-1216451004088320000),
    ((0,2,6,13),-1703031405723648000),
    ((0,2,5,14),-2189611807358976000),
    ((0,2,4,15),-2676192208994304000),
    ((0,2,3,16),-3162772610629632000),
    ((0,1,2,18),4135933413900288000)
  ]

private def accP19 : List Term := [
    ((0,1,9,11),-243290200817664000),
    ((0,1,8,12),-486580401635328000),
    ((0,1,7,13),-729870602452992000),
    ((0,1,6,14),-973160803270656000),
    ((0,1,5,15),-1216451004088320000),
    ((0,1,4,16),-1459741204905984000),
    ((0,1,3,17),-1703031405723648000),
    ((0,1,2,18),-1946321606541312000)
  ]

private theorem normalCheckP18 : normalizeTermsFast (sourceBlock 20 20 1 18)=normalP18 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP18 : mergeTerms accP18 normalP18=accP19 := by
  decide +kernel

private def normalP19 : List Term := [
    ((0,1,9,11),243290200817664000),
    ((0,1,8,12),486580401635328000),
    ((0,1,7,13),729870602452992000),
    ((0,1,6,14),973160803270656000),
    ((0,1,5,15),1216451004088320000),
    ((0,1,4,16),1459741204905984000),
    ((0,1,3,17),1703031405723648000),
    ((0,1,2,18),1946321606541312000)
  ]

private theorem normalCheckP19 : normalizeTermsFast (sourceBlock 20 20 1 19)=normalP19 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP19 : mergeTerms accP19 normalP19=sourceGroupEndD20R01G04S04 := by
  decide +kernel

theorem sourceGroupCheckD20R01G04S04 :
    foldNormalBlocks sourceGroupStartD20R01G04S04
      [sourceBlock 20 20 1 16,sourceBlock 20 20 1 17,sourceBlock 20 20 1 18,sourceBlock 20 20 1 19]=sourceGroupEndD20R01G04S04 := by
  rw [foldNormalBlocks,normalCheckP16,mergeCheckP16]
  rw [foldNormalBlocks,normalCheckP17,mergeCheckP17]
  rw [foldNormalBlocks,normalCheckP18,mergeCheckP18]
  rw [foldNormalBlocks,normalCheckP19,mergeCheckP19]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceGroupCheckD20R01G04S04
