import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD23R05
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R05G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R05G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R05G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R05G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R05G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R05G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 23 23 5)=sourceGroupEndD23R05G05S04 := by
  change foldNormalBlocks sourceGroupStartD23R05G00S04 ([sourceBlock 23 23 5 0,sourceBlock 23 23 5 1,sourceBlock 23 23 5 2,sourceBlock 23 23 5 3] ++ ([sourceBlock 23 23 5 4,sourceBlock 23 23 5 5,sourceBlock 23 23 5 6,sourceBlock 23 23 5 7] ++ ([sourceBlock 23 23 5 8,sourceBlock 23 23 5 9,sourceBlock 23 23 5 10,sourceBlock 23 23 5 11] ++ ([sourceBlock 23 23 5 12,sourceBlock 23 23 5 13,sourceBlock 23 23 5 14,sourceBlock 23 23 5 15] ++ ([sourceBlock 23 23 5 16,sourceBlock 23 23 5 17,sourceBlock 23 23 5 18,sourceBlock 23 23 5 19] ++ ([sourceBlock 23 23 5 20,sourceBlock 23 23 5 21,sourceBlock 23 23 5 22,sourceBlock 23 23 5 23]))))))=sourceGroupEndD23R05G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD23R05G00S04]
  have boundary00 : sourceGroupEndD23R05G00S04 =
      sourceGroupStartD23R05G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R05G01S04]
  have boundary01 : sourceGroupEndD23R05G01S04 =
      sourceGroupStartD23R05G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R05G02S04]
  have boundary02 : sourceGroupEndD23R05G02S04 =
      sourceGroupStartD23R05G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R05G03S04]
  have boundary03 : sourceGroupEndD23R05G03S04 =
      sourceGroupStartD23R05G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R05G04S04]
  have boundary04 : sourceGroupEndD23R05G04S04 =
      sourceGroupStartD23R05G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD23R05G05S04

theorem sourceDirectCheckD23R05 :
    alternateIntegerFourWords (integerSourceWords 23 23 5)=
      alternateIntegerFourWords (integerSlaterWords 23 5) := by
  apply originalSlaterMode_of_blocks_check 23 5 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD23R05,slaterNormalCheckD23R05]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD23R05
