import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks

/-! Contiguous original p blocks, each original normalized block and
prefix merge checked independently in the kernel. Raw source literals are omitted;
normalization is computed directly from the unchanged original sourceBlock. The arbitrary literal
start becomes an actual source prefix only through the final fold proof. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

def sourceGroupStartD20R03G00S04 : List Term := []

def sourceGroupEndD20R03G00S04 : List Term := [
    ((1,3,8,9),-34145993097216000),
    ((0,4,8,9),-68291986194432000),
    ((1,3,7,10),-85364982743040000),
    ((0,4,7,10),-170729965486080000),
    ((1,2,8,10),34145993097216000),
    ((0,3,8,10),102437979291648000),
    ((0,2,9,10),-38414242234368000),
    ((1,3,6,11),-85364982743040000),
    ((0,4,6,11),-170729965486080000),
    ((1,2,7,11),51218989645824000),
    ((0,3,7,11),153656968937472000),
    ((0,2,8,11),-98169730154496000),
    ((0,1,9,11),38414242234368000),
    ((1,2,6,12),34145993097216000),
    ((0,3,6,12),102437979291648000),
    ((0,2,7,12),-106706228428800000),
    ((0,1,8,12),59755487920128000),
    ((1,3,4,13),204875958583296000),
    ((1,2,5,13),-34145993097216000),
    ((0,3,5,13),-102437979291648000),
    ((0,2,6,13),-29877743960064000),
    ((0,1,7,13),46950740508672000),
    ((1,2,4,14),-170729965486080000),
    ((0,3,4,14),-1639007668666368000),
    ((0,2,5,14),166461716348928000),
    ((0,1,6,14),-17072996548608000),
    ((1,2,3,15),-1502423696277504000),
    ((0,2,4,15),-1703031405723648000),
    ((0,1,5,15),-149388719800320000),
    ((0,2,3,16),3205455102001152000),
    ((0,1,4,16),-4123128666488832000),
    ((0,1,3,17),5698112598097920000),
    ((0,1,2,18),-5698112598097920000)
  ]

private def normalP00 : List Term := [
    ((0,1,9,11),38414242234368000),
    ((0,1,8,12),59755487920128000),
    ((0,1,7,13),46950740508672000),
    ((0,1,6,14),-17072996548608000),
    ((0,1,5,15),-149388719800320000),
    ((0,1,4,16),-367069425795072000),
    ((0,1,3,17),-687188111081472000),
    ((0,1,2,18),-1126817772208128000)
  ]

private def accP01 : List Term := [
    ((0,1,9,11),38414242234368000),
    ((0,1,8,12),59755487920128000),
    ((0,1,7,13),46950740508672000),
    ((0,1,6,14),-17072996548608000),
    ((0,1,5,15),-149388719800320000),
    ((0,1,4,16),-367069425795072000),
    ((0,1,3,17),-687188111081472000),
    ((0,1,2,18),-1126817772208128000)
  ]

private theorem normalCheckP00 : normalizeTermsFast (sourceBlock 20 20 3 0)=normalP00 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP00 : mergeTerms sourceGroupStartD20R03G00S04 normalP00=accP01 := by
  decide +kernel

private def normalP01 : List Term := [
    ((0,2,9,10),-38414242234368000),
    ((0,2,8,11),-98169730154496000),
    ((0,2,7,12),-106706228428800000),
    ((0,2,6,13),-29877743960064000),
    ((0,2,5,14),166461716348928000),
    ((0,2,4,15),516458145595392000),
    ((0,2,3,16),1054257536876544000),
    ((0,1,2,18),-2829849177931776000)
  ]

private def accP02 : List Term := [
    ((0,2,9,10),-38414242234368000),
    ((0,2,8,11),-98169730154496000),
    ((0,1,9,11),38414242234368000),
    ((0,2,7,12),-106706228428800000),
    ((0,1,8,12),59755487920128000),
    ((0,2,6,13),-29877743960064000),
    ((0,1,7,13),46950740508672000),
    ((0,2,5,14),166461716348928000),
    ((0,1,6,14),-17072996548608000),
    ((0,2,4,15),516458145595392000),
    ((0,1,5,15),-149388719800320000),
    ((0,2,3,16),1054257536876544000),
    ((0,1,4,16),-367069425795072000),
    ((0,1,3,17),-687188111081472000),
    ((0,1,2,18),-3956666950139904000)
  ]

private theorem normalCheckP01 : normalizeTermsFast (sourceBlock 20 20 3 1)=normalP01 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP01 : mergeTerms accP01 normalP01=accP02 := by
  decide +kernel

private def normalP02 : List Term := [
    ((1,2,8,10),34145993097216000),
    ((0,3,8,10),102437979291648000),
    ((1,2,7,11),51218989645824000),
    ((0,3,7,11),153656968937472000),
    ((1,2,6,12),34145993097216000),
    ((0,3,6,12),102437979291648000),
    ((1,2,5,13),-34145993097216000),
    ((0,3,5,13),-102437979291648000),
    ((1,2,4,14),-170729965486080000),
    ((0,3,4,14),-512189896458240000),
    ((1,2,3,15),-392678920617984000),
    ((0,2,3,16),2151197565124608000),
    ((0,1,3,17),3482891295916032000),
    ((0,1,2,18),-1741445647958016000)
  ]

private def accP03 : List Term := [
    ((1,2,8,10),34145993097216000),
    ((0,3,8,10),102437979291648000),
    ((0,2,9,10),-38414242234368000),
    ((1,2,7,11),51218989645824000),
    ((0,3,7,11),153656968937472000),
    ((0,2,8,11),-98169730154496000),
    ((0,1,9,11),38414242234368000),
    ((1,2,6,12),34145993097216000),
    ((0,3,6,12),102437979291648000),
    ((0,2,7,12),-106706228428800000),
    ((0,1,8,12),59755487920128000),
    ((1,2,5,13),-34145993097216000),
    ((0,3,5,13),-102437979291648000),
    ((0,2,6,13),-29877743960064000),
    ((0,1,7,13),46950740508672000),
    ((1,2,4,14),-170729965486080000),
    ((0,3,4,14),-512189896458240000),
    ((0,2,5,14),166461716348928000),
    ((0,1,6,14),-17072996548608000),
    ((1,2,3,15),-392678920617984000),
    ((0,2,4,15),516458145595392000),
    ((0,1,5,15),-149388719800320000),
    ((0,2,3,16),3205455102001152000),
    ((0,1,4,16),-367069425795072000),
    ((0,1,3,17),2795703184834560000),
    ((0,1,2,18),-5698112598097920000)
  ]

private theorem normalCheckP02 : normalizeTermsFast (sourceBlock 20 20 3 2)=normalP02 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP02 : mergeTerms accP02 normalP02=accP03 := by
  decide +kernel

private def normalP03 : List Term := [
    ((1,3,8,9),-34145993097216000),
    ((0,4,8,9),-68291986194432000),
    ((1,3,7,10),-85364982743040000),
    ((0,4,7,10),-170729965486080000),
    ((1,3,6,11),-85364982743040000),
    ((0,4,6,11),-170729965486080000),
    ((1,3,4,13),204875958583296000),
    ((0,3,4,14),-1126817772208128000),
    ((1,2,3,15),-1109744775659520000),
    ((0,2,4,15),-2219489551319040000),
    ((0,1,4,16),-3756059240693760000),
    ((0,1,3,17),2902409413263360000)
  ]

private theorem normalCheckP03 : normalizeTermsFast (sourceBlock 20 20 3 3)=normalP03 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP03 : mergeTerms accP03 normalP03=sourceGroupEndD20R03G00S04 := by
  decide +kernel

theorem sourceGroupCheckD20R03G00S04 :
    foldNormalBlocks sourceGroupStartD20R03G00S04
      [sourceBlock 20 20 3 0,sourceBlock 20 20 3 1,sourceBlock 20 20 3 2,sourceBlock 20 20 3 3]=sourceGroupEndD20R03G00S04 := by
  rw [foldNormalBlocks,normalCheckP00,mergeCheckP00]
  rw [foldNormalBlocks,normalCheckP01,mergeCheckP01]
  rw [foldNormalBlocks,normalCheckP02,mergeCheckP02]
  rw [foldNormalBlocks,normalCheckP03,mergeCheckP03]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceGroupCheckD20R03G00S04
