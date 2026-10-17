import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD21R05
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R05G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R05G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R05G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R05G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R05G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R05G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 21 21 5)=sourceGroupEndD21R05G05S04 := by
  change foldNormalBlocks sourceGroupStartD21R05G00S04 ([sourceBlock 21 21 5 0,sourceBlock 21 21 5 1,sourceBlock 21 21 5 2,sourceBlock 21 21 5 3] ++ ([sourceBlock 21 21 5 4,sourceBlock 21 21 5 5,sourceBlock 21 21 5 6,sourceBlock 21 21 5 7] ++ ([sourceBlock 21 21 5 8,sourceBlock 21 21 5 9,sourceBlock 21 21 5 10,sourceBlock 21 21 5 11] ++ ([sourceBlock 21 21 5 12,sourceBlock 21 21 5 13,sourceBlock 21 21 5 14,sourceBlock 21 21 5 15] ++ ([sourceBlock 21 21 5 16,sourceBlock 21 21 5 17,sourceBlock 21 21 5 18,sourceBlock 21 21 5 19] ++ ([sourceBlock 21 21 5 20,sourceBlock 21 21 5 21]))))))=sourceGroupEndD21R05G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD21R05G00S04]
  have boundary00 : sourceGroupEndD21R05G00S04 =
      sourceGroupStartD21R05G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD21R05G01S04]
  have boundary01 : sourceGroupEndD21R05G01S04 =
      sourceGroupStartD21R05G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD21R05G02S04]
  have boundary02 : sourceGroupEndD21R05G02S04 =
      sourceGroupStartD21R05G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD21R05G03S04]
  have boundary03 : sourceGroupEndD21R05G03S04 =
      sourceGroupStartD21R05G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD21R05G04S04]
  have boundary04 : sourceGroupEndD21R05G04S04 =
      sourceGroupStartD21R05G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD21R05G05S04

theorem sourceDirectCheckD21R05 :
    alternateIntegerFourWords (integerSourceWords 21 21 5)=
      alternateIntegerFourWords (integerSlaterWords 21 5) := by
  apply originalSlaterMode_of_blocks_check 21 5 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD21R05,slaterNormalCheckD21R05]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD21R05
