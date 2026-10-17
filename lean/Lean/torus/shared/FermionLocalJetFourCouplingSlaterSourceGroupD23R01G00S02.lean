import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks

/-! Contiguous original p blocks, each coefficient list, sorted block and
prefix merge checked independently in the kernel. The arbitrary literal
start becomes an actual source prefix only through the final fold proof. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

def sourceGroupStartD23R01G00S02 : List Term := []

def sourceGroupEndD23R01G00S02 : List Term := [
    ((0,2,10,12),-4496002911110430720000),
    ((0,1,11,12),1124000727777607680000),
    ((0,2,9,13),-8992005822220861440000),
    ((0,1,10,13),3372002183332823040000),
    ((0,2,8,14),-13488008733331292160000),
    ((0,1,9,14),5620003638888038400000),
    ((0,2,7,15),-17984011644441722880000),
    ((0,1,8,15),7868005094443253760000),
    ((0,2,6,16),-22480014555552153600000),
    ((0,1,7,16),10116006549998469120000),
    ((0,2,5,17),-26976017466662584320000),
    ((0,1,6,17),12364008005553684480000),
    ((0,2,4,18),-31472020377773015040000),
    ((0,1,5,18),14612009461108899840000),
    ((0,2,3,19),-35968023288883445760000),
    ((0,1,4,19),16860010916664115200000),
    ((0,1,3,20),19108012372219330560000),
    ((0,1,2,21),66316042938878853120000)
  ]

private def rawP00 : List Term := [
    ((0,1,0,23),25852016738884976640000),
    ((1,0,0,23),0),
    ((0,1,1,22),23604015283329761280000),
    ((1,0,1,22),0),
    ((0,1,2,21),21356013827774545920000),
    ((1,0,2,21),0),
    ((0,1,3,20),19108012372219330560000),
    ((1,0,3,20),0),
    ((0,1,4,19),16860010916664115200000),
    ((1,0,4,19),0),
    ((0,1,5,18),14612009461108899840000),
    ((1,0,5,18),0),
    ((0,1,6,17),12364008005553684480000),
    ((1,0,6,17),0),
    ((0,1,7,16),10116006549998469120000),
    ((1,0,7,16),0),
    ((0,1,8,15),7868005094443253760000),
    ((1,0,8,15),0),
    ((0,1,9,14),5620003638888038400000),
    ((1,0,9,14),0),
    ((0,1,10,13),3372002183332823040000),
    ((1,0,10,13),0),
    ((0,1,11,12),1124000727777607680000),
    ((1,0,11,12),0)
  ]

private def normalP00 : List Term := [
    ((0,1,11,12),1124000727777607680000),
    ((0,1,10,13),3372002183332823040000),
    ((0,1,9,14),5620003638888038400000),
    ((0,1,8,15),7868005094443253760000),
    ((0,1,7,16),10116006549998469120000),
    ((0,1,6,17),12364008005553684480000),
    ((0,1,5,18),14612009461108899840000),
    ((0,1,4,19),16860010916664115200000),
    ((0,1,3,20),19108012372219330560000),
    ((0,1,2,21),21356013827774545920000)
  ]

private def accP01 : List Term := [
    ((0,1,11,12),1124000727777607680000),
    ((0,1,10,13),3372002183332823040000),
    ((0,1,9,14),5620003638888038400000),
    ((0,1,8,15),7868005094443253760000),
    ((0,1,7,16),10116006549998469120000),
    ((0,1,6,17),12364008005553684480000),
    ((0,1,5,18),14612009461108899840000),
    ((0,1,4,19),16860010916664115200000),
    ((0,1,3,20),19108012372219330560000),
    ((0,1,2,21),21356013827774545920000)
  ]

private theorem rawCheckP00 : sourceBlock 23 23 1 0=rawP00 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem normalCheckP00 : normalizeTermsFast (sourceBlock 23 23 1 0)=normalP00 := by
  rw [rawCheckP00]
  decide +kernel

private theorem mergeCheckP00 : mergeTerms sourceGroupStartD23R01G00S02 normalP00=accP01 := by
  decide +kernel

private def rawP01 : List Term := [
    ((0,2,0,22),-49456032022214737920000),
    ((1,1,0,22),0),
    ((2,0,0,22),0),
    ((0,2,1,21),-44960029111104307200000),
    ((1,1,1,21),0),
    ((2,0,1,21),0),
    ((0,2,2,20),-40464026199993876480000),
    ((1,1,2,20),0),
    ((2,0,2,20),0),
    ((0,2,3,19),-35968023288883445760000),
    ((1,1,3,19),0),
    ((2,0,3,19),0),
    ((0,2,4,18),-31472020377773015040000),
    ((1,1,4,18),0),
    ((2,0,4,18),0),
    ((0,2,5,17),-26976017466662584320000),
    ((1,1,5,17),0),
    ((2,0,5,17),0),
    ((0,2,6,16),-22480014555552153600000),
    ((1,1,6,16),0),
    ((2,0,6,16),0),
    ((0,2,7,15),-17984011644441722880000),
    ((1,1,7,15),0),
    ((2,0,7,15),0),
    ((0,2,8,14),-13488008733331292160000),
    ((1,1,8,14),0),
    ((2,0,8,14),0),
    ((0,2,9,13),-8992005822220861440000),
    ((1,1,9,13),0),
    ((2,0,9,13),0),
    ((0,2,10,12),-4496002911110430720000),
    ((1,1,10,12),0),
    ((2,0,10,12),0)
  ]

private def normalP01 : List Term := [
    ((0,2,10,12),-4496002911110430720000),
    ((0,2,9,13),-8992005822220861440000),
    ((0,2,8,14),-13488008733331292160000),
    ((0,2,7,15),-17984011644441722880000),
    ((0,2,6,16),-22480014555552153600000),
    ((0,2,5,17),-26976017466662584320000),
    ((0,2,4,18),-31472020377773015040000),
    ((0,2,3,19),-35968023288883445760000),
    ((0,1,2,21),44960029111104307200000)
  ]

private theorem rawCheckP01 : sourceBlock 23 23 1 1=rawP01 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem normalCheckP01 : normalizeTermsFast (sourceBlock 23 23 1 1)=normalP01 := by
  rw [rawCheckP01]
  decide +kernel

private theorem mergeCheckP01 : mergeTerms accP01 normalP01=sourceGroupEndD23R01G00S02 := by
  decide +kernel

theorem sourceGroupCheckD23R01G00S02 :
    foldNormalBlocks sourceGroupStartD23R01G00S02
      [sourceBlock 23 23 1 0,sourceBlock 23 23 1 1]=sourceGroupEndD23R01G00S02 := by
  rw [foldNormalBlocks,normalCheckP00,mergeCheckP00]
  rw [foldNormalBlocks,normalCheckP01,mergeCheckP01]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceGroupCheckD23R01G00S02
