import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD22R01
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R01G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R01G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R01G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R01G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R01G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R01G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 22 22 1)=sourceGroupEndD22R01G05S04 := by
  change foldNormalBlocks sourceGroupStartD22R01G00S04 ([sourceBlock 22 22 1 0,sourceBlock 22 22 1 1,sourceBlock 22 22 1 2,sourceBlock 22 22 1 3] ++ ([sourceBlock 22 22 1 4,sourceBlock 22 22 1 5,sourceBlock 22 22 1 6,sourceBlock 22 22 1 7] ++ ([sourceBlock 22 22 1 8,sourceBlock 22 22 1 9,sourceBlock 22 22 1 10,sourceBlock 22 22 1 11] ++ ([sourceBlock 22 22 1 12,sourceBlock 22 22 1 13,sourceBlock 22 22 1 14,sourceBlock 22 22 1 15] ++ ([sourceBlock 22 22 1 16,sourceBlock 22 22 1 17,sourceBlock 22 22 1 18,sourceBlock 22 22 1 19] ++ ([sourceBlock 22 22 1 20,sourceBlock 22 22 1 21,sourceBlock 22 22 1 22]))))))=sourceGroupEndD22R01G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD22R01G00S04]
  have boundary00 : sourceGroupEndD22R01G00S04 =
      sourceGroupStartD22R01G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R01G01S04]
  have boundary01 : sourceGroupEndD22R01G01S04 =
      sourceGroupStartD22R01G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R01G02S04]
  have boundary02 : sourceGroupEndD22R01G02S04 =
      sourceGroupStartD22R01G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R01G03S04]
  have boundary03 : sourceGroupEndD22R01G03S04 =
      sourceGroupStartD22R01G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R01G04S04]
  have boundary04 : sourceGroupEndD22R01G04S04 =
      sourceGroupStartD22R01G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD22R01G05S04

theorem sourceDirectCheckD22R01 :
    alternateIntegerFourWords (integerSourceWords 22 22 1)=
      alternateIntegerFourWords (integerSlaterWords 22 1) := by
  apply originalSlaterMode_of_blocks_check 22 1 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD22R01,slaterNormalCheckD22R01]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD22R01
