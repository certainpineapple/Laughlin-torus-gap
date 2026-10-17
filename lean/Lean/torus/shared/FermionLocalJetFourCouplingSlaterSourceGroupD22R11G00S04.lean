import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks

/-! Contiguous original p blocks, each original normalized block and
prefix merge checked independently in the kernel. Raw source literals are omitted;
normalization is computed directly from the unchanged original sourceBlock. The arbitrary literal
start becomes an actual source prefix only through the final fold proof. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

def sourceGroupStartD22R11G00S04 : List Term := []

def sourceGroupEndD22R11G00S04 : List Term := [
    ((1,3,9,10),-401524432404480000),
    ((0,4,9,10),-803048864808960000),
    ((1,3,8,11),-312296780759040000),
    ((0,4,8,11),-624593561518080000),
    ((1,2,9,11),401524432404480000),
    ((0,3,9,11),1204573297213440000),
    ((0,2,10,11),-803048864808960000),
    ((1,3,7,12),669207387340800000),
    ((0,4,7,12),1338414774681600000),
    ((1,2,8,12),-89227651645440000),
    ((0,3,8,12),-267682954936320000),
    ((0,2,9,12),-803048864808960000),
    ((0,1,10,12),803048864808960000),
    ((1,3,6,13),248562743869440000),
    ((0,4,6,13),497125487738880000),
    ((1,2,7,13),-579979735695360000),
    ((0,3,7,13),-1739939207086080000),
    ((0,2,8,13),1159959471390720000),
    ((1,3,5,14),-1574230711173120000),
    ((0,4,5,14),-3148461422346240000),
    ((1,2,6,14),331416991825920000),
    ((0,3,6,14),994250975477760000),
    ((0,2,7,14),1159959471390720000),
    ((0,1,8,14),-1159959471390720000),
    ((1,3,4,15),248562743869440000),
    ((1,2,5,15),1242813719347200000),
    ((0,3,5,15),3728441158041600000),
    ((0,2,6,15),-2485627438694400000),
    ((1,2,4,16),-1491376463216640000),
    ((0,3,4,16),-15908015607644160000),
    ((0,2,5,16),-2485627438694400000),
    ((0,1,6,16),2485627438694400000),
    ((1,2,3,17),2817044430520320000),
    ((0,2,4,17),22536355444162560000),
    ((0,2,3,18),-25353399874682880000),
    ((0,1,4,18),67609066332487680000),
    ((0,1,3,19),160571532539658240000),
    ((0,1,2,20),-160571532539658240000)
  ]

private def normalP00 : List Term := [
    ((0,1,10,12),803048864808960000),
    ((0,1,8,14),-1159959471390720000),
    ((0,1,6,16),2485627438694400000),
    ((0,1,4,18),-8451133291560960000),
    ((0,1,2,20),53523844179886080000)
  ]

private def accP01 : List Term := [
    ((0,1,10,12),803048864808960000),
    ((0,1,8,14),-1159959471390720000),
    ((0,1,6,16),2485627438694400000),
    ((0,1,4,18),-8451133291560960000),
    ((0,1,2,20),53523844179886080000)
  ]

private theorem normalCheckP00 : normalizeTermsFast (sourceBlock 22 22 11 0)=normalP00 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP00 : mergeTerms sourceGroupStartD22R11G00S04 normalP00=accP01 := by
  decide +kernel

private def normalP01 : List Term := [
    ((0,2,10,11),-803048864808960000),
    ((0,2,9,12),-803048864808960000),
    ((0,2,8,13),1159959471390720000),
    ((0,2,7,14),1159959471390720000),
    ((0,2,6,15),-2485627438694400000),
    ((0,2,5,16),-2485627438694400000),
    ((0,2,4,17),8451133291560960000),
    ((0,2,3,18),8451133291560960000),
    ((0,1,2,20),53523844179886080000)
  ]

private def accP02 : List Term := [
    ((0,2,10,11),-803048864808960000),
    ((0,2,9,12),-803048864808960000),
    ((0,1,10,12),803048864808960000),
    ((0,2,8,13),1159959471390720000),
    ((0,2,7,14),1159959471390720000),
    ((0,1,8,14),-1159959471390720000),
    ((0,2,6,15),-2485627438694400000),
    ((0,2,5,16),-2485627438694400000),
    ((0,1,6,16),2485627438694400000),
    ((0,2,4,17),8451133291560960000),
    ((0,2,3,18),8451133291560960000),
    ((0,1,4,18),-8451133291560960000),
    ((0,1,2,20),107047688359772160000)
  ]

private theorem normalCheckP01 : normalizeTermsFast (sourceBlock 22 22 11 1)=normalP01 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP01 : mergeTerms accP01 normalP01=accP02 := by
  decide +kernel

private def normalP02 : List Term := [
    ((1,2,9,11),401524432404480000),
    ((0,3,9,11),1204573297213440000),
    ((1,2,8,12),-89227651645440000),
    ((0,3,8,12),-267682954936320000),
    ((1,2,7,13),-579979735695360000),
    ((0,3,7,13),-1739939207086080000),
    ((1,2,6,14),331416991825920000),
    ((0,3,6,14),994250975477760000),
    ((1,2,5,15),1242813719347200000),
    ((0,3,5,15),3728441158041600000),
    ((1,2,4,16),-1491376463216640000),
    ((0,3,4,16),-4474129389649920000),
    ((1,2,3,17),-4225566645780480000),
    ((0,2,3,18),-33804533166243840000),
    ((0,1,3,19),-80285766269829120000),
    ((0,1,2,20),-267619220899430400000)
  ]

private def accP03 : List Term := [
    ((1,2,9,11),401524432404480000),
    ((0,3,9,11),1204573297213440000),
    ((0,2,10,11),-803048864808960000),
    ((1,2,8,12),-89227651645440000),
    ((0,3,8,12),-267682954936320000),
    ((0,2,9,12),-803048864808960000),
    ((0,1,10,12),803048864808960000),
    ((1,2,7,13),-579979735695360000),
    ((0,3,7,13),-1739939207086080000),
    ((0,2,8,13),1159959471390720000),
    ((1,2,6,14),331416991825920000),
    ((0,3,6,14),994250975477760000),
    ((0,2,7,14),1159959471390720000),
    ((0,1,8,14),-1159959471390720000),
    ((1,2,5,15),1242813719347200000),
    ((0,3,5,15),3728441158041600000),
    ((0,2,6,15),-2485627438694400000),
    ((1,2,4,16),-1491376463216640000),
    ((0,3,4,16),-4474129389649920000),
    ((0,2,5,16),-2485627438694400000),
    ((0,1,6,16),2485627438694400000),
    ((1,2,3,17),-4225566645780480000),
    ((0,2,4,17),8451133291560960000),
    ((0,2,3,18),-25353399874682880000),
    ((0,1,4,18),-8451133291560960000),
    ((0,1,3,19),-80285766269829120000),
    ((0,1,2,20),-160571532539658240000)
  ]

private theorem normalCheckP02 : normalizeTermsFast (sourceBlock 22 22 11 2)=normalP02 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP02 : mergeTerms accP02 normalP02=accP03 := by
  decide +kernel

private def normalP03 : List Term := [
    ((1,3,9,10),-401524432404480000),
    ((0,4,9,10),-803048864808960000),
    ((1,3,8,11),-312296780759040000),
    ((0,4,8,11),-624593561518080000),
    ((1,3,7,12),669207387340800000),
    ((0,4,7,12),1338414774681600000),
    ((1,3,6,13),248562743869440000),
    ((0,4,6,13),497125487738880000),
    ((1,3,5,14),-1574230711173120000),
    ((0,4,5,14),-3148461422346240000),
    ((1,3,4,15),248562743869440000),
    ((0,3,4,16),-11433886217994240000),
    ((1,2,3,17),7042611076300800000),
    ((0,2,4,17),14085222152601600000),
    ((0,1,4,18),76060199624048640000),
    ((0,1,3,19),240857298809487360000)
  ]

private theorem normalCheckP03 : normalizeTermsFast (sourceBlock 22 22 11 3)=normalP03 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP03 : mergeTerms accP03 normalP03=sourceGroupEndD22R11G00S04 := by
  decide +kernel

theorem sourceGroupCheckD22R11G00S04 :
    foldNormalBlocks sourceGroupStartD22R11G00S04
      [sourceBlock 22 22 11 0,sourceBlock 22 22 11 1,sourceBlock 22 22 11 2,sourceBlock 22 22 11 3]=sourceGroupEndD22R11G00S04 := by
  rw [foldNormalBlocks,normalCheckP00,mergeCheckP00]
  rw [foldNormalBlocks,normalCheckP01,mergeCheckP01]
  rw [foldNormalBlocks,normalCheckP02,mergeCheckP02]
  rw [foldNormalBlocks,normalCheckP03,mergeCheckP03]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceGroupCheckD22R11G00S04
