import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD23R09
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R09G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R09G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R09G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R09G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R09G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R09G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 23 23 9)=sourceGroupEndD23R09G05S04 := by
  change foldNormalBlocks sourceGroupStartD23R09G00S04 ([sourceBlock 23 23 9 0,sourceBlock 23 23 9 1,sourceBlock 23 23 9 2,sourceBlock 23 23 9 3] ++ ([sourceBlock 23 23 9 4,sourceBlock 23 23 9 5,sourceBlock 23 23 9 6,sourceBlock 23 23 9 7] ++ ([sourceBlock 23 23 9 8,sourceBlock 23 23 9 9,sourceBlock 23 23 9 10,sourceBlock 23 23 9 11] ++ ([sourceBlock 23 23 9 12,sourceBlock 23 23 9 13,sourceBlock 23 23 9 14,sourceBlock 23 23 9 15] ++ ([sourceBlock 23 23 9 16,sourceBlock 23 23 9 17,sourceBlock 23 23 9 18,sourceBlock 23 23 9 19] ++ ([sourceBlock 23 23 9 20,sourceBlock 23 23 9 21,sourceBlock 23 23 9 22,sourceBlock 23 23 9 23]))))))=sourceGroupEndD23R09G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD23R09G00S04]
  have boundary00 : sourceGroupEndD23R09G00S04 =
      sourceGroupStartD23R09G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R09G01S04]
  have boundary01 : sourceGroupEndD23R09G01S04 =
      sourceGroupStartD23R09G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R09G02S04]
  have boundary02 : sourceGroupEndD23R09G02S04 =
      sourceGroupStartD23R09G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R09G03S04]
  have boundary03 : sourceGroupEndD23R09G03S04 =
      sourceGroupStartD23R09G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R09G04S04]
  have boundary04 : sourceGroupEndD23R09G04S04 =
      sourceGroupStartD23R09G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD23R09G05S04

theorem sourceDirectCheckD23R09 :
    alternateIntegerFourWords (integerSourceWords 23 23 9)=
      alternateIntegerFourWords (integerSlaterWords 23 9) := by
  apply originalSlaterMode_of_blocks_check 23 9 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD23R09,slaterNormalCheckD23R09]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD23R09
