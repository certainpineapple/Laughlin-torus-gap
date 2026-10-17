import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks

/-! Contiguous original p blocks, each original normalized block and
prefix merge checked independently in the kernel. Raw source literals are omitted;
normalization is computed directly from the unchanged original sourceBlock. The arbitrary literal
start becomes an actual source prefix only through the final fold proof. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

def sourceGroupStartD20R05G00S04 : List Term := []

def sourceGroupEndD20R05G00S04 : List Term := [
    ((1,3,8,9),8787571752960000),
    ((0,4,8,9),17575143505920000),
    ((1,3,7,10),17575143505920000),
    ((0,4,7,10),35150287011840000),
    ((1,2,8,10),-8787571752960000),
    ((0,3,8,10),-26362715258880000),
    ((0,2,9,10),11298306539520000),
    ((1,3,6,11),5021469573120000),
    ((0,4,6,11),10042939146240000),
    ((1,2,7,11),-8787571752960000),
    ((0,3,7,11),-26362715258880000),
    ((0,2,8,11),23851980472320000),
    ((0,1,9,11),-11298306539520000),
    ((1,3,5,12),-26362715258880000),
    ((0,4,5,12),-52725430517760000),
    ((1,2,6,12),3766102179840000),
    ((0,3,6,12),11298306539520000),
    ((0,2,7,12),11298306539520000),
    ((0,1,8,12),-12553673932800000),
    ((1,3,4,13),-48959328337920000),
    ((1,2,5,13),22596613079040000),
    ((0,3,5,13),67789839237120000),
    ((0,2,6,13),-26362715258880000),
    ((0,1,7,13),1255367393280000),
    ((1,2,4,14),26362715258880000),
    ((0,3,4,14),79088145776640000),
    ((0,2,5,14),-64023737057280000),
    ((0,1,6,14),25107347865600000),
    ((1,2,3,15),-254839580835840000),
    ((0,2,4,15),-498380855132160000),
    ((0,1,5,15),38916389191680000),
    ((0,2,3,16),753220435968000000),
    ((0,1,4,16),-1596827324252160000),
    ((0,1,3,17),3585329275207680000),
    ((0,1,2,18),-3585329275207680000)
  ]

private def normalP00 : List Term := [
    ((0,1,9,11),-11298306539520000),
    ((0,1,8,12),-12553673932800000),
    ((0,1,7,13),1255367393280000),
    ((0,1,6,14),25107347865600000),
    ((0,1,5,15),38916389191680000),
    ((0,1,4,16),2510734786560000),
    ((0,1,3,17),-149388719800320000),
    ((0,1,2,18),-512189896458240000)
  ]

private def accP01 : List Term := [
    ((0,1,9,11),-11298306539520000),
    ((0,1,8,12),-12553673932800000),
    ((0,1,7,13),1255367393280000),
    ((0,1,6,14),25107347865600000),
    ((0,1,5,15),38916389191680000),
    ((0,1,4,16),2510734786560000),
    ((0,1,3,17),-149388719800320000),
    ((0,1,2,18),-512189896458240000)
  ]

private theorem normalCheckP00 : normalizeTermsFast (sourceBlock 20 20 5 0)=normalP00 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP00 : mergeTerms sourceGroupStartD20R05G00S04 normalP00=accP01 := by
  decide +kernel

private def normalP01 : List Term := [
    ((0,2,9,10),11298306539520000),
    ((0,2,8,11),23851980472320000),
    ((0,2,7,12),11298306539520000),
    ((0,2,6,13),-26362715258880000),
    ((0,2,5,14),-64023737057280000),
    ((0,2,4,15),-41427123978240000),
    ((0,2,3,16),146877985013760000),
    ((0,1,2,18),-1728640900546560000)
  ]

private def accP02 : List Term := [
    ((0,2,9,10),11298306539520000),
    ((0,2,8,11),23851980472320000),
    ((0,1,9,11),-11298306539520000),
    ((0,2,7,12),11298306539520000),
    ((0,1,8,12),-12553673932800000),
    ((0,2,6,13),-26362715258880000),
    ((0,1,7,13),1255367393280000),
    ((0,2,5,14),-64023737057280000),
    ((0,1,6,14),25107347865600000),
    ((0,2,4,15),-41427123978240000),
    ((0,1,5,15),38916389191680000),
    ((0,2,3,16),146877985013760000),
    ((0,1,4,16),2510734786560000),
    ((0,1,3,17),-149388719800320000),
    ((0,1,2,18),-2240830797004800000)
  ]

private theorem normalCheckP01 : normalizeTermsFast (sourceBlock 20 20 5 1)=normalP01 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP01 : mergeTerms accP01 normalP01=accP02 := by
  decide +kernel

private def normalP02 : List Term := [
    ((1,2,8,10),-8787571752960000),
    ((0,3,8,10),-26362715258880000),
    ((1,2,7,11),-8787571752960000),
    ((0,3,7,11),-26362715258880000),
    ((1,2,6,12),3766102179840000),
    ((0,3,6,12),11298306539520000),
    ((1,2,5,13),22596613079040000),
    ((0,3,5,13),67789839237120000),
    ((1,2,4,14),26362715258880000),
    ((0,3,4,14),79088145776640000),
    ((1,2,3,15),-26362715258880000),
    ((0,2,3,16),606342450954240000),
    ((0,1,3,17),1792664637603840000),
    ((0,1,2,18),-1344498478202880000)
  ]

private def accP03 : List Term := [
    ((1,2,8,10),-8787571752960000),
    ((0,3,8,10),-26362715258880000),
    ((0,2,9,10),11298306539520000),
    ((1,2,7,11),-8787571752960000),
    ((0,3,7,11),-26362715258880000),
    ((0,2,8,11),23851980472320000),
    ((0,1,9,11),-11298306539520000),
    ((1,2,6,12),3766102179840000),
    ((0,3,6,12),11298306539520000),
    ((0,2,7,12),11298306539520000),
    ((0,1,8,12),-12553673932800000),
    ((1,2,5,13),22596613079040000),
    ((0,3,5,13),67789839237120000),
    ((0,2,6,13),-26362715258880000),
    ((0,1,7,13),1255367393280000),
    ((1,2,4,14),26362715258880000),
    ((0,3,4,14),79088145776640000),
    ((0,2,5,14),-64023737057280000),
    ((0,1,6,14),25107347865600000),
    ((1,2,3,15),-26362715258880000),
    ((0,2,4,15),-41427123978240000),
    ((0,1,5,15),38916389191680000),
    ((0,2,3,16),753220435968000000),
    ((0,1,4,16),2510734786560000),
    ((0,1,3,17),1643275917803520000),
    ((0,1,2,18),-3585329275207680000)
  ]

private theorem normalCheckP02 : normalizeTermsFast (sourceBlock 20 20 5 2)=normalP02 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP02 : mergeTerms accP02 normalP02=accP03 := by
  decide +kernel

private def normalP03 : List Term := [
    ((1,3,8,9),8787571752960000),
    ((0,4,8,9),17575143505920000),
    ((1,3,7,10),17575143505920000),
    ((0,4,7,10),35150287011840000),
    ((1,3,6,11),5021469573120000),
    ((0,4,6,11),10042939146240000),
    ((1,3,5,12),-26362715258880000),
    ((0,4,5,12),-52725430517760000),
    ((1,3,4,13),-48959328337920000),
    ((1,2,3,15),-228476865576960000),
    ((0,2,4,15),-456953731153920000),
    ((0,1,4,16),-1599338059038720000),
    ((0,1,3,17),1942053357404160000)
  ]

private theorem normalCheckP03 : normalizeTermsFast (sourceBlock 20 20 5 3)=normalP03 := by
  simp only [sourceBlock,pairCoefficientList,coefficientList,Nat.choose_eq_fast_choose]
  decide +kernel

private theorem mergeCheckP03 : mergeTerms accP03 normalP03=sourceGroupEndD20R05G00S04 := by
  decide +kernel

theorem sourceGroupCheckD20R05G00S04 :
    foldNormalBlocks sourceGroupStartD20R05G00S04
      [sourceBlock 20 20 5 0,sourceBlock 20 20 5 1,sourceBlock 20 20 5 2,sourceBlock 20 20 5 3]=sourceGroupEndD20R05G00S04 := by
  rw [foldNormalBlocks,normalCheckP00,mergeCheckP00]
  rw [foldNormalBlocks,normalCheckP01,mergeCheckP01]
  rw [foldNormalBlocks,normalCheckP02,mergeCheckP02]
  rw [foldNormalBlocks,normalCheckP03,mergeCheckP03]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceGroupCheckD20R05G00S04
