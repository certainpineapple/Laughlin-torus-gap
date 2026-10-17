import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks

/-! Contiguous original p blocks, each original normalized block and
prefix merge checked independently in the kernel. Raw source literals are omitted;
normalization is computed directly from the unchanged original sourceBlock. The arbitrary literal
start becomes an actual source prefix only through the final fold proof. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

def sourceGroupStartD20R09G00S04 : List Term := []

def sourceGroupEndD20R09G00S04 : List Term := [
    ((1,3,8,9),2027901173760000),
    ((0,4,8,9),4055802347520000),
    ((1,3,7,10),2027901173760000),
    ((0,4,7,10),4055802347520000),
    ((1,2,8,10),-2027901173760000),
    ((0,3,8,10),-6083703521280000),
    ((0,2,9,10),3650222112768000),
    ((1,3,6,11),-3186701844480000),
    ((0,4,6,11),-6373403688960000),
    ((0,2,8,11),4461382582272000),
    ((0,1,9,11),-3650222112768000),
    ((1,3,5,12),-3186701844480000),
    ((0,4,5,12),-6373403688960000),
    ((1,2,6,12),3186701844480000),
    ((0,3,6,12),9560105533440000),
    ((0,2,7,12),-4461382582272000),
    ((0,1,8,12),-811160469504000),
    ((1,3,4,13),8285424795648000),
    ((0,2,6,13),-8285424795648000),
    ((0,1,7,13),5272543051776000),
    ((1,2,4,14),-8285424795648000),
    ((0,3,4,14),-41427123978240000),
    ((0,2,5,14),8285424795648000),
    ((0,1,6,14),3012881743872000),
    ((1,2,3,15),41427123978240000),
    ((0,2,4,15),107710522343424000),
    ((0,1,5,15),-11298306539520000),
    ((0,2,3,16),-149137646321664000),
    ((0,1,4,16),69296280109056000),
    ((0,1,3,17),742675349864448000),
    ((0,1,2,18),-742675349864448000)
  ]

private def normalP00 : List Term := [
    ((0,1,9,11),-3650222112768000),
    ((0,1,8,12),-811160469504000),
    ((0,1,7,13),5272543051776000),
    ((0,1,6,14),3012881743872000),
    ((0,1,5,15),-11298306539520000),
    ((0,1,4,16),-13557967847424000),
    ((0,1,3,17),38414242234368000),
    ((0,1,2,18),102437979291648000)
  ]

private def accP01 : List Term := [
    ((0,1,9,11),-3650222112768000),
    ((0,1,8,12),-811160469504000),
    ((0,1,7,13),5272543051776000),
    ((0,1,6,14),3012881743872000),
    ((0,1,5,15),-11298306539520000),
    ((0,1,4,16),-13557967847424000),
    ((0,1,3,17),38414242234368000),
    ((0,1,2,18),102437979291648000)
  ]

private theorem normalCheckP00 : normalizeTermsFast (sourceBlock 20 20 9 0)=normalP00 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP00 : mergeTerms sourceGroupStartD20R09G00S04 normalP00=accP01 := by
  decide +kernel

private def normalP01 : List Term := [
    ((0,2,9,10),3650222112768000),
    ((0,2,8,11),4461382582272000),
    ((0,2,7,12),-4461382582272000),
    ((0,2,6,13),-8285424795648000),
    ((0,2,5,14),8285424795648000),
    ((0,2,4,15),24856274386944000),
    ((0,2,3,16),-24856274386944000),
    ((0,1,2,18),-140852221526016000)
  ]

private def accP02 : List Term := [
    ((0,2,9,10),3650222112768000),
    ((0,2,8,11),4461382582272000),
    ((0,1,9,11),-3650222112768000),
    ((0,2,7,12),-4461382582272000),
    ((0,1,8,12),-811160469504000),
    ((0,2,6,13),-8285424795648000),
    ((0,1,7,13),5272543051776000),
    ((0,2,5,14),8285424795648000),
    ((0,1,6,14),3012881743872000),
    ((0,2,4,15),24856274386944000),
    ((0,1,5,15),-11298306539520000),
    ((0,2,3,16),-24856274386944000),
    ((0,1,4,16),-13557967847424000),
    ((0,1,3,17),38414242234368000),
    ((0,1,2,18),-38414242234368000)
  ]

private theorem normalCheckP01 : normalizeTermsFast (sourceBlock 20 20 9 1)=normalP01 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP01 : mergeTerms accP01 normalP01=accP02 := by
  decide +kernel

private def normalP02 : List Term := [
    ((1,2,8,10),-2027901173760000),
    ((0,3,8,10),-6083703521280000),
    ((1,2,6,12),3186701844480000),
    ((0,3,6,12),9560105533440000),
    ((1,2,4,14),-8285424795648000),
    ((0,3,4,14),-24856274386944000),
    ((0,2,3,16),-124281371934720000),
    ((0,1,2,18),-704261107630080000)
  ]

private def accP03 : List Term := [
    ((1,2,8,10),-2027901173760000),
    ((0,3,8,10),-6083703521280000),
    ((0,2,9,10),3650222112768000),
    ((0,2,8,11),4461382582272000),
    ((0,1,9,11),-3650222112768000),
    ((1,2,6,12),3186701844480000),
    ((0,3,6,12),9560105533440000),
    ((0,2,7,12),-4461382582272000),
    ((0,1,8,12),-811160469504000),
    ((0,2,6,13),-8285424795648000),
    ((0,1,7,13),5272543051776000),
    ((1,2,4,14),-8285424795648000),
    ((0,3,4,14),-24856274386944000),
    ((0,2,5,14),8285424795648000),
    ((0,1,6,14),3012881743872000),
    ((0,2,4,15),24856274386944000),
    ((0,1,5,15),-11298306539520000),
    ((0,2,3,16),-149137646321664000),
    ((0,1,4,16),-13557967847424000),
    ((0,1,3,17),38414242234368000),
    ((0,1,2,18),-742675349864448000)
  ]

private theorem normalCheckP02 : normalizeTermsFast (sourceBlock 20 20 9 2)=normalP02 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP02 : mergeTerms accP02 normalP02=accP03 := by
  decide +kernel

private def normalP03 : List Term := [
    ((1,3,8,9),2027901173760000),
    ((0,4,8,9),4055802347520000),
    ((1,3,7,10),2027901173760000),
    ((0,4,7,10),4055802347520000),
    ((1,3,6,11),-3186701844480000),
    ((0,4,6,11),-6373403688960000),
    ((1,3,5,12),-3186701844480000),
    ((0,4,5,12),-6373403688960000),
    ((1,3,4,13),8285424795648000),
    ((0,3,4,14),-16570849591296000),
    ((1,2,3,15),41427123978240000),
    ((0,2,4,15),82854247956480000),
    ((0,1,4,16),82854247956480000),
    ((0,1,3,17),704261107630080000)
  ]

private theorem normalCheckP03 : normalizeTermsFast (sourceBlock 20 20 9 3)=normalP03 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP03 : mergeTerms accP03 normalP03=sourceGroupEndD20R09G00S04 := by
  decide +kernel

theorem sourceGroupCheckD20R09G00S04 :
    foldNormalBlocks sourceGroupStartD20R09G00S04
      [sourceBlock 20 20 9 0,sourceBlock 20 20 9 1,sourceBlock 20 20 9 2,sourceBlock 20 20 9 3]=sourceGroupEndD20R09G00S04 := by
  rw [foldNormalBlocks,normalCheckP00,mergeCheckP00]
  rw [foldNormalBlocks,normalCheckP01,mergeCheckP01]
  rw [foldNormalBlocks,normalCheckP02,mergeCheckP02]
  rw [foldNormalBlocks,normalCheckP03,mergeCheckP03]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceGroupCheckD20R09G00S04
