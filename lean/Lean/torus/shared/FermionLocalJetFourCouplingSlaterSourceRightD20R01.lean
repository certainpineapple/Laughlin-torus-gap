import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

def slaterWitnessD20R01 : List Term := [
    ((0,1,2,18),0),
    ((0,1,3,17),0),
    ((0,1,4,16),0),
    ((0,1,5,15),0),
    ((0,1,6,14),0),
    ((0,1,7,13),0),
    ((0,1,8,12),0),
    ((0,1,9,11),0),
    ((0,2,3,16),0),
    ((0,2,4,15),0),
    ((0,2,5,14),0),
    ((0,2,6,13),0),
    ((0,2,7,12),0),
    ((0,2,8,11),0),
    ((0,2,9,10),0),
    ((0,3,4,14),0),
    ((0,3,5,13),0),
    ((0,3,6,12),0),
    ((0,3,7,11),0),
    ((0,3,8,10),0),
    ((0,4,5,12),0),
    ((0,4,6,11),0),
    ((0,4,7,10),0),
    ((0,4,8,9),0),
    ((0,5,6,10),0),
    ((0,5,7,9),0),
    ((0,6,7,8),0),
    ((1,2,3,15),0),
    ((1,2,4,14),0),
    ((1,2,5,13),0),
    ((1,2,6,12),0),
    ((1,2,7,11),0),
    ((1,2,8,10),0),
    ((1,3,4,13),0),
    ((1,3,5,12),0),
    ((1,3,6,11),0),
    ((1,3,7,10),0),
    ((1,3,8,9),0),
    ((1,4,5,11),0),
    ((1,4,6,10),0),
    ((1,4,7,9),0),
    ((1,5,6,9),0),
    ((1,5,7,8),0),
    ((2,3,4,12),0),
    ((2,3,5,11),0),
    ((2,3,6,10),0),
    ((2,3,7,9),0),
    ((2,4,5,10),0),
    ((2,4,6,9),0),
    ((2,4,7,8),0),
    ((2,5,6,8),0),
    ((3,4,5,9),0),
    ((3,4,6,8),0),
    ((3,5,6,7),0)
  ]

def slaterNormalWitnessD20R01 : List Term := []

theorem slaterWitnessCheckD20R01 : slaterTerms 20 1=slaterWitnessD20R01 := by
  simp only [slaterTerms,integerSlaterNumerator,OAI.Laughlin.Certificate.V,
    OAI.Laughlin.Certificate.U,Nat.choose_eq_fast_choose]
  decide +kernel

theorem slaterNormalCheckD20R01 : normalizeTermsFast slaterWitnessD20R01=slaterNormalWitnessD20R01 := by
  decide +kernel

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.slaterWitnessCheckD20R01
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.slaterNormalCheckD20R01
