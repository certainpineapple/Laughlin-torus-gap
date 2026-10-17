import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD22R13
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R13G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R13G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R13G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R13G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R13G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R13G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 22 22 13)=sourceGroupEndD22R13G05S04 := by
  change foldNormalBlocks sourceGroupStartD22R13G00S04 ([sourceBlock 22 22 13 0,sourceBlock 22 22 13 1,sourceBlock 22 22 13 2,sourceBlock 22 22 13 3] ++ ([sourceBlock 22 22 13 4,sourceBlock 22 22 13 5,sourceBlock 22 22 13 6,sourceBlock 22 22 13 7] ++ ([sourceBlock 22 22 13 8,sourceBlock 22 22 13 9,sourceBlock 22 22 13 10,sourceBlock 22 22 13 11] ++ ([sourceBlock 22 22 13 12,sourceBlock 22 22 13 13,sourceBlock 22 22 13 14,sourceBlock 22 22 13 15] ++ ([sourceBlock 22 22 13 16,sourceBlock 22 22 13 17,sourceBlock 22 22 13 18,sourceBlock 22 22 13 19] ++ ([sourceBlock 22 22 13 20,sourceBlock 22 22 13 21,sourceBlock 22 22 13 22]))))))=sourceGroupEndD22R13G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD22R13G00S04]
  have boundary00 : sourceGroupEndD22R13G00S04 =
      sourceGroupStartD22R13G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R13G01S04]
  have boundary01 : sourceGroupEndD22R13G01S04 =
      sourceGroupStartD22R13G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R13G02S04]
  have boundary02 : sourceGroupEndD22R13G02S04 =
      sourceGroupStartD22R13G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R13G03S04]
  have boundary03 : sourceGroupEndD22R13G03S04 =
      sourceGroupStartD22R13G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R13G04S04]
  have boundary04 : sourceGroupEndD22R13G04S04 =
      sourceGroupStartD22R13G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD22R13G05S04

theorem sourceDirectCheckD22R13 :
    alternateIntegerFourWords (integerSourceWords 22 22 13)=
      alternateIntegerFourWords (integerSlaterWords 22 13) := by
  apply originalSlaterMode_of_blocks_check 22 13 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD22R13,slaterNormalCheckD22R13]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD22R13
