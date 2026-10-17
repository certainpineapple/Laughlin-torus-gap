import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD22R09
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R09G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R09G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R09G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R09G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R09G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R09G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 22 22 9)=sourceGroupEndD22R09G05S04 := by
  change foldNormalBlocks sourceGroupStartD22R09G00S04 ([sourceBlock 22 22 9 0,sourceBlock 22 22 9 1,sourceBlock 22 22 9 2,sourceBlock 22 22 9 3] ++ ([sourceBlock 22 22 9 4,sourceBlock 22 22 9 5,sourceBlock 22 22 9 6,sourceBlock 22 22 9 7] ++ ([sourceBlock 22 22 9 8,sourceBlock 22 22 9 9,sourceBlock 22 22 9 10,sourceBlock 22 22 9 11] ++ ([sourceBlock 22 22 9 12,sourceBlock 22 22 9 13,sourceBlock 22 22 9 14,sourceBlock 22 22 9 15] ++ ([sourceBlock 22 22 9 16,sourceBlock 22 22 9 17,sourceBlock 22 22 9 18,sourceBlock 22 22 9 19] ++ ([sourceBlock 22 22 9 20,sourceBlock 22 22 9 21,sourceBlock 22 22 9 22]))))))=sourceGroupEndD22R09G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD22R09G00S04]
  have boundary00 : sourceGroupEndD22R09G00S04 =
      sourceGroupStartD22R09G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R09G01S04]
  have boundary01 : sourceGroupEndD22R09G01S04 =
      sourceGroupStartD22R09G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R09G02S04]
  have boundary02 : sourceGroupEndD22R09G02S04 =
      sourceGroupStartD22R09G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R09G03S04]
  have boundary03 : sourceGroupEndD22R09G03S04 =
      sourceGroupStartD22R09G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R09G04S04]
  have boundary04 : sourceGroupEndD22R09G04S04 =
      sourceGroupStartD22R09G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD22R09G05S04

theorem sourceDirectCheckD22R09 :
    alternateIntegerFourWords (integerSourceWords 22 22 9)=
      alternateIntegerFourWords (integerSlaterWords 22 9) := by
  apply originalSlaterMode_of_blocks_check 22 9 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD22R09,slaterNormalCheckD22R09]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD22R09
