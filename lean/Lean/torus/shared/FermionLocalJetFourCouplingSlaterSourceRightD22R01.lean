import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

def slaterWitnessD22R01 : List Term := [
    ((0,1,2,20),0),
    ((0,1,3,19),0),
    ((0,1,4,18),0),
    ((0,1,5,17),0),
    ((0,1,6,16),0),
    ((0,1,7,15),0),
    ((0,1,8,14),0),
    ((0,1,9,13),0),
    ((0,1,10,12),0),
    ((0,2,3,18),0),
    ((0,2,4,17),0),
    ((0,2,5,16),0),
    ((0,2,6,15),0),
    ((0,2,7,14),0),
    ((0,2,8,13),0),
    ((0,2,9,12),0),
    ((0,2,10,11),0),
    ((0,3,4,16),0),
    ((0,3,5,15),0),
    ((0,3,6,14),0),
    ((0,3,7,13),0),
    ((0,3,8,12),0),
    ((0,3,9,11),0),
    ((0,4,5,14),0),
    ((0,4,6,13),0),
    ((0,4,7,12),0),
    ((0,4,8,11),0),
    ((0,4,9,10),0),
    ((0,5,6,12),0),
    ((0,5,7,11),0),
    ((0,5,8,10),0),
    ((0,6,7,10),0),
    ((0,6,8,9),0),
    ((1,2,3,17),0),
    ((1,2,4,16),0),
    ((1,2,5,15),0),
    ((1,2,6,14),0),
    ((1,2,7,13),0),
    ((1,2,8,12),0),
    ((1,2,9,11),0),
    ((1,3,4,15),0),
    ((1,3,5,14),0),
    ((1,3,6,13),0),
    ((1,3,7,12),0),
    ((1,3,8,11),0),
    ((1,3,9,10),0),
    ((1,4,5,13),0),
    ((1,4,6,12),0),
    ((1,4,7,11),0),
    ((1,4,8,10),0),
    ((1,5,6,11),0),
    ((1,5,7,10),0),
    ((1,5,8,9),0),
    ((1,6,7,9),0),
    ((2,3,4,14),0),
    ((2,3,5,13),0),
    ((2,3,6,12),0),
    ((2,3,7,11),0),
    ((2,3,8,10),0),
    ((2,4,5,12),0),
    ((2,4,6,11),0),
    ((2,4,7,10),0),
    ((2,4,8,9),0),
    ((2,5,6,10),0),
    ((2,5,7,9),0),
    ((2,6,7,8),0),
    ((3,4,5,11),0),
    ((3,4,6,10),0),
    ((3,4,7,9),0),
    ((3,5,6,9),0),
    ((3,5,7,8),0),
    ((4,5,6,8),0)
  ]

def slaterNormalWitnessD22R01 : List Term := []

theorem slaterWitnessCheckD22R01 : slaterTerms 22 1=slaterWitnessD22R01 := by
  simp only [slaterTerms,integerSlaterNumerator,OAI.Laughlin.Certificate.V,
    OAI.Laughlin.Certificate.U,Nat.choose_eq_fast_choose]
  decide +kernel

theorem slaterNormalCheckD22R01 : normalizeTermsFast slaterWitnessD22R01=slaterNormalWitnessD22R01 := by
  decide +kernel

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.slaterWitnessCheckD22R01
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.slaterNormalCheckD22R01
