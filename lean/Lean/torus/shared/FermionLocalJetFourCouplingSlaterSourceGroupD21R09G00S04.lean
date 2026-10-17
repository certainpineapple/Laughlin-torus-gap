import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks

/-! Contiguous original p blocks, each original normalized block and
prefix merge checked independently in the kernel. Raw source literals are omitted;
normalization is computed directly from the unchanged original sourceBlock. The arbitrary literal
start becomes an actual source prefix only through the final fold proof. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

def sourceGroupStartD21R09G00S04 : List Term := []

def sourceGroupEndD21R09G00S04 : List Term := [
    ((1,3,8,10),-48669628170240000),
    ((0,4,8,10),-97339256340480000),
    ((1,2,9,10),21901332676608000),
    ((0,3,9,10),65703998029824000),
    ((1,2,8,11),26768295493632000),
    ((0,3,8,11),80304886480896000),
    ((0,2,9,11),-87605330706432000),
    ((0,1,10,11),36502221127680000),
    ((1,3,6,12),76480844267520000),
    ((0,4,6,12),152961688535040000),
    ((1,2,7,12),-26768295493632000),
    ((0,3,7,12),-80304886480896000),
    ((0,2,8,12),-19467851268096000),
    ((0,1,9,12),51103109578752000),
    ((1,2,6,13),-49712548773888000),
    ((0,3,6,13),-149137646321664000),
    ((0,2,7,13),126541033242624000),
    ((0,1,8,13),-31635258310656000),
    ((1,3,4,14),-198850195095552000),
    ((1,2,5,14),49712548773888000),
    ((0,3,5,14),149137646321664000),
    ((0,2,6,14),72309161852928000),
    ((0,1,7,14),-94905774931968000),
    ((1,2,4,15),149137646321664000),
    ((0,3,4,15),447412938964992000),
    ((0,2,5,15),-271159356948480000),
    ((0,1,6,15),22596613079040000),
    ((1,2,3,16),-1143388621799424000),
    ((0,2,4,16),-2313893179293696000),
    ((0,1,5,16),248562743869440000),
    ((0,2,3,17),3457281801093120000),
    ((0,1,4,17),76828484468736000),
    ((0,1,3,18),-20436376868683776000),
    ((0,1,2,19),20436376868683776000)
  ]

private def normalP00 : List Term := [
    ((0,1,10,11),36502221127680000),
    ((0,1,9,12),51103109578752000),
    ((0,1,8,13),-31635258310656000),
    ((0,1,7,14),-94905774931968000),
    ((0,1,6,15),22596613079040000),
    ((0,1,5,16),248562743869440000),
    ((0,1,4,17),76828484468736000),
    ((0,1,3,18),-998770298093568000),
    ((0,1,2,19),-1459741204905984000)
  ]

private def accP01 : List Term := [
    ((0,1,10,11),36502221127680000),
    ((0,1,9,12),51103109578752000),
    ((0,1,8,13),-31635258310656000),
    ((0,1,7,14),-94905774931968000),
    ((0,1,6,15),22596613079040000),
    ((0,1,5,16),248562743869440000),
    ((0,1,4,17),76828484468736000),
    ((0,1,3,18),-998770298093568000),
    ((0,1,2,19),-1459741204905984000)
  ]

private theorem normalCheckP00 : normalizeTermsFast (sourceBlock 21 21 9 0)=normalP00 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP00 : mergeTerms sourceGroupStartD21R09G00S04 normalP00=accP01 := by
  decide +kernel

private def normalP01 : List Term := [
    ((0,2,9,11),-87605330706432000),
    ((0,2,8,12),-19467851268096000),
    ((0,2,7,13),126541033242624000),
    ((0,2,6,14),72309161852928000),
    ((0,2,5,15),-271159356948480000),
    ((0,2,4,16),-325391228338176000),
    ((0,2,3,17),921941813624832000),
    ((0,1,2,19),5838964819623936000)
  ]

private def accP02 : List Term := [
    ((0,2,9,11),-87605330706432000),
    ((0,1,10,11),36502221127680000),
    ((0,2,8,12),-19467851268096000),
    ((0,1,9,12),51103109578752000),
    ((0,2,7,13),126541033242624000),
    ((0,1,8,13),-31635258310656000),
    ((0,2,6,14),72309161852928000),
    ((0,1,7,14),-94905774931968000),
    ((0,2,5,15),-271159356948480000),
    ((0,1,6,15),22596613079040000),
    ((0,2,4,16),-325391228338176000),
    ((0,1,5,16),248562743869440000),
    ((0,2,3,17),921941813624832000),
    ((0,1,4,17),76828484468736000),
    ((0,1,3,18),-998770298093568000),
    ((0,1,2,19),4379223614717952000)
  ]

private theorem normalCheckP01 : normalizeTermsFast (sourceBlock 21 21 9 1)=normalP01 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP01 : mergeTerms accP01 normalP01=accP02 := by
  decide +kernel

private def normalP02 : List Term := [
    ((1,2,9,10),21901332676608000),
    ((0,3,9,10),65703998029824000),
    ((1,2,8,11),26768295493632000),
    ((0,3,8,11),80304886480896000),
    ((1,2,7,12),-26768295493632000),
    ((0,3,7,12),-80304886480896000),
    ((1,2,6,13),-49712548773888000),
    ((0,3,6,13),-149137646321664000),
    ((1,2,5,14),49712548773888000),
    ((0,3,5,14),149137646321664000),
    ((1,2,4,15),149137646321664000),
    ((0,3,4,15),447412938964992000),
    ((1,2,3,16),-149137646321664000),
    ((0,2,3,17),2535339987468288000),
    ((0,1,3,18),-2535339987468288000),
    ((0,1,2,19),16057153253965824000)
  ]

private def accP03 : List Term := [
    ((1,2,9,10),21901332676608000),
    ((0,3,9,10),65703998029824000),
    ((1,2,8,11),26768295493632000),
    ((0,3,8,11),80304886480896000),
    ((0,2,9,11),-87605330706432000),
    ((0,1,10,11),36502221127680000),
    ((1,2,7,12),-26768295493632000),
    ((0,3,7,12),-80304886480896000),
    ((0,2,8,12),-19467851268096000),
    ((0,1,9,12),51103109578752000),
    ((1,2,6,13),-49712548773888000),
    ((0,3,6,13),-149137646321664000),
    ((0,2,7,13),126541033242624000),
    ((0,1,8,13),-31635258310656000),
    ((1,2,5,14),49712548773888000),
    ((0,3,5,14),149137646321664000),
    ((0,2,6,14),72309161852928000),
    ((0,1,7,14),-94905774931968000),
    ((1,2,4,15),149137646321664000),
    ((0,3,4,15),447412938964992000),
    ((0,2,5,15),-271159356948480000),
    ((0,1,6,15),22596613079040000),
    ((1,2,3,16),-149137646321664000),
    ((0,2,4,16),-325391228338176000),
    ((0,1,5,16),248562743869440000),
    ((0,2,3,17),3457281801093120000),
    ((0,1,4,17),76828484468736000),
    ((0,1,3,18),-3534110285561856000),
    ((0,1,2,19),20436376868683776000)
  ]

private theorem normalCheckP02 : normalizeTermsFast (sourceBlock 21 21 9 2)=normalP02 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP02 : mergeTerms accP02 normalP02=accP03 := by
  decide +kernel

private def normalP03 : List Term := [
    ((1,3,8,10),-48669628170240000),
    ((0,4,8,10),-97339256340480000),
    ((1,3,6,12),76480844267520000),
    ((0,4,6,12),152961688535040000),
    ((1,3,4,14),-198850195095552000),
    ((1,2,3,16),-994250975477760000),
    ((0,2,4,16),-1988501950955520000),
    ((0,1,3,18),-16902266583121920000)
  ]

private theorem normalCheckP03 : normalizeTermsFast (sourceBlock 21 21 9 3)=normalP03 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP03 : mergeTerms accP03 normalP03=sourceGroupEndD21R09G00S04 := by
  decide +kernel

theorem sourceGroupCheckD21R09G00S04 :
    foldNormalBlocks sourceGroupStartD21R09G00S04
      [sourceBlock 21 21 9 0,sourceBlock 21 21 9 1,sourceBlock 21 21 9 2,sourceBlock 21 21 9 3]=sourceGroupEndD21R09G00S04 := by
  rw [foldNormalBlocks,normalCheckP00,mergeCheckP00]
  rw [foldNormalBlocks,normalCheckP01,mergeCheckP01]
  rw [foldNormalBlocks,normalCheckP02,mergeCheckP02]
  rw [foldNormalBlocks,normalCheckP03,mergeCheckP03]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceGroupCheckD21R09G00S04
