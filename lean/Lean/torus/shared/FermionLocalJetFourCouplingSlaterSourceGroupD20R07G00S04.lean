import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks

/-! Contiguous original p blocks, each original normalized block and
prefix merge checked independently in the kernel. Raw source literals are omitted;
normalization is computed directly from the unchanged original sourceBlock. The arbitrary literal
start becomes an actual source prefix only through the final fold proof. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

def sourceGroupStartD20R07G00S04 : List Term := []

def sourceGroupEndD20R07G00S04 : List Term := [
    ((1,3,8,9),-3515028701184000),
    ((0,4,8,9),-7030057402368000),
    ((1,3,7,10),-5272543051776000),
    ((0,4,7,10),-10545086103552000),
    ((1,2,8,10),3515028701184000),
    ((0,3,8,10),10545086103552000),
    ((0,2,9,10),-5272543051776000),
    ((1,3,6,11),2761808265216000),
    ((0,4,6,11),5523616530432000),
    ((1,2,7,11),1757514350592000),
    ((0,3,7,11),5272543051776000),
    ((0,2,8,11),-8787571752960000),
    ((0,1,9,11),5272543051776000),
    ((1,3,5,12),11047233060864000),
    ((0,4,5,12),22094466121728000),
    ((1,2,6,12),-4519322615808000),
    ((0,3,6,12),-13557967847424000),
    ((0,2,7,12),1757514350592000),
    ((0,1,8,12),3515028701184000),
    ((1,2,5,13),-6527910445056000),
    ((0,3,5,13),-19583731335168000),
    ((0,2,6,13),16319776112640000),
    ((0,1,7,13),-5272543051776000),
    ((1,2,4,14),6527910445056000),
    ((0,3,4,14),91390746230784000),
    ((0,2,5,14),9791865667584000),
    ((0,1,6,14),-11047233060864000),
    ((1,2,3,15),65279104450560000),
    ((0,2,4,15),35903507447808000),
    ((0,1,5,15),1255367393280000),
    ((0,2,3,16),-101182611898368000),
    ((0,1,4,16),-396193949319168000),
    ((0,1,3,17),1933516859129856000),
    ((0,1,2,18),-1933516859129856000)
  ]

private def normalP00 : List Term := [
    ((0,1,9,11),5272543051776000),
    ((0,1,8,12),3515028701184000),
    ((0,1,7,13),-5272543051776000),
    ((0,1,6,14),-11047233060864000),
    ((0,1,5,15),1255367393280000),
    ((0,1,4,16),34648140054528000),
    ((0,1,3,17),46950740508672000),
    ((0,1,2,18),-102437979291648000)
  ]

private def accP01 : List Term := [
    ((0,1,9,11),5272543051776000),
    ((0,1,8,12),3515028701184000),
    ((0,1,7,13),-5272543051776000),
    ((0,1,6,14),-11047233060864000),
    ((0,1,5,15),1255367393280000),
    ((0,1,4,16),34648140054528000),
    ((0,1,3,17),46950740508672000),
    ((0,1,2,18),-102437979291648000)
  ]

private theorem normalCheckP00 : normalizeTermsFast (sourceBlock 20 20 7 0)=normalP00 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP00 : mergeTerms sourceGroupStartD20R07G00S04 normalP00=accP01 := by
  decide +kernel

private def normalP01 : List Term := [
    ((0,2,9,10),-5272543051776000),
    ((0,2,8,11),-8787571752960000),
    ((0,2,7,12),1757514350592000),
    ((0,2,6,13),16319776112640000),
    ((0,2,5,14),9791865667584000),
    ((0,2,4,15),-35903507447808000),
    ((0,2,3,16),-81598880563200000),
    ((0,1,2,18),-832308581744640000)
  ]

private def accP02 : List Term := [
    ((0,2,9,10),-5272543051776000),
    ((0,2,8,11),-8787571752960000),
    ((0,1,9,11),5272543051776000),
    ((0,2,7,12),1757514350592000),
    ((0,1,8,12),3515028701184000),
    ((0,2,6,13),16319776112640000),
    ((0,1,7,13),-5272543051776000),
    ((0,2,5,14),9791865667584000),
    ((0,1,6,14),-11047233060864000),
    ((0,2,4,15),-35903507447808000),
    ((0,1,5,15),1255367393280000),
    ((0,2,3,16),-81598880563200000),
    ((0,1,4,16),34648140054528000),
    ((0,1,3,17),46950740508672000),
    ((0,1,2,18),-934746561036288000)
  ]

private theorem normalCheckP01 : normalizeTermsFast (sourceBlock 20 20 7 1)=normalP01 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP01 : mergeTerms accP01 normalP01=accP02 := by
  decide +kernel

private def normalP02 : List Term := [
    ((1,2,8,10),3515028701184000),
    ((0,3,8,10),10545086103552000),
    ((1,2,7,11),1757514350592000),
    ((0,3,7,11),5272543051776000),
    ((1,2,6,12),-4519322615808000),
    ((0,3,6,12),-13557967847424000),
    ((1,2,5,13),-6527910445056000),
    ((0,3,5,13),-19583731335168000),
    ((1,2,4,14),6527910445056000),
    ((0,3,4,14),19583731335168000),
    ((1,2,3,15),29375597002752000),
    ((0,2,3,16),-19583731335168000),
    ((0,1,3,17),665846865395712000),
    ((0,1,2,18),-998770298093568000)
  ]

private def accP03 : List Term := [
    ((1,2,8,10),3515028701184000),
    ((0,3,8,10),10545086103552000),
    ((0,2,9,10),-5272543051776000),
    ((1,2,7,11),1757514350592000),
    ((0,3,7,11),5272543051776000),
    ((0,2,8,11),-8787571752960000),
    ((0,1,9,11),5272543051776000),
    ((1,2,6,12),-4519322615808000),
    ((0,3,6,12),-13557967847424000),
    ((0,2,7,12),1757514350592000),
    ((0,1,8,12),3515028701184000),
    ((1,2,5,13),-6527910445056000),
    ((0,3,5,13),-19583731335168000),
    ((0,2,6,13),16319776112640000),
    ((0,1,7,13),-5272543051776000),
    ((1,2,4,14),6527910445056000),
    ((0,3,4,14),19583731335168000),
    ((0,2,5,14),9791865667584000),
    ((0,1,6,14),-11047233060864000),
    ((1,2,3,15),29375597002752000),
    ((0,2,4,15),-35903507447808000),
    ((0,1,5,15),1255367393280000),
    ((0,2,3,16),-101182611898368000),
    ((0,1,4,16),34648140054528000),
    ((0,1,3,17),712797605904384000),
    ((0,1,2,18),-1933516859129856000)
  ]

private theorem normalCheckP02 : normalizeTermsFast (sourceBlock 20 20 7 2)=normalP02 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP02 : mergeTerms accP02 normalP02=accP03 := by
  decide +kernel

private def normalP03 : List Term := [
    ((1,3,8,9),-3515028701184000),
    ((0,4,8,9),-7030057402368000),
    ((1,3,7,10),-5272543051776000),
    ((0,4,7,10),-10545086103552000),
    ((1,3,6,11),2761808265216000),
    ((0,4,6,11),5523616530432000),
    ((1,3,5,12),11047233060864000),
    ((0,4,5,12),22094466121728000),
    ((0,3,4,14),71807014895616000),
    ((1,2,3,15),35903507447808000),
    ((0,2,4,15),71807014895616000),
    ((0,1,4,16),-430842089373696000),
    ((0,1,3,17),1220719253225472000)
  ]

private theorem normalCheckP03 : normalizeTermsFast (sourceBlock 20 20 7 3)=normalP03 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP03 : mergeTerms accP03 normalP03=sourceGroupEndD20R07G00S04 := by
  decide +kernel

theorem sourceGroupCheckD20R07G00S04 :
    foldNormalBlocks sourceGroupStartD20R07G00S04
      [sourceBlock 20 20 7 0,sourceBlock 20 20 7 1,sourceBlock 20 20 7 2,sourceBlock 20 20 7 3]=sourceGroupEndD20R07G00S04 := by
  rw [foldNormalBlocks,normalCheckP00,mergeCheckP00]
  rw [foldNormalBlocks,normalCheckP01,mergeCheckP01]
  rw [foldNormalBlocks,normalCheckP02,mergeCheckP02]
  rw [foldNormalBlocks,normalCheckP03,mergeCheckP03]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceGroupCheckD20R07G00S04
