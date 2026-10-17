import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD20R09
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R09G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R09G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R09G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R09G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R09G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R09G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 20 20 9)=sourceGroupEndD20R09G05S04 := by
  change foldNormalBlocks sourceGroupStartD20R09G00S04 ([sourceBlock 20 20 9 0,sourceBlock 20 20 9 1,sourceBlock 20 20 9 2,sourceBlock 20 20 9 3] ++ ([sourceBlock 20 20 9 4,sourceBlock 20 20 9 5,sourceBlock 20 20 9 6,sourceBlock 20 20 9 7] ++ ([sourceBlock 20 20 9 8,sourceBlock 20 20 9 9,sourceBlock 20 20 9 10,sourceBlock 20 20 9 11] ++ ([sourceBlock 20 20 9 12,sourceBlock 20 20 9 13,sourceBlock 20 20 9 14,sourceBlock 20 20 9 15] ++ ([sourceBlock 20 20 9 16,sourceBlock 20 20 9 17,sourceBlock 20 20 9 18,sourceBlock 20 20 9 19] ++ ([sourceBlock 20 20 9 20]))))))=sourceGroupEndD20R09G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD20R09G00S04]
  have boundary00 : sourceGroupEndD20R09G00S04 =
      sourceGroupStartD20R09G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD20R09G01S04]
  have boundary01 : sourceGroupEndD20R09G01S04 =
      sourceGroupStartD20R09G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD20R09G02S04]
  have boundary02 : sourceGroupEndD20R09G02S04 =
      sourceGroupStartD20R09G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD20R09G03S04]
  have boundary03 : sourceGroupEndD20R09G03S04 =
      sourceGroupStartD20R09G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD20R09G04S04]
  have boundary04 : sourceGroupEndD20R09G04S04 =
      sourceGroupStartD20R09G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD20R09G05S04

theorem sourceDirectCheckD20R09 :
    alternateIntegerFourWords (integerSourceWords 20 20 9)=
      alternateIntegerFourWords (integerSlaterWords 20 9) := by
  apply originalSlaterMode_of_blocks_check 20 9 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD20R09,slaterNormalCheckD20R09]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD20R09
