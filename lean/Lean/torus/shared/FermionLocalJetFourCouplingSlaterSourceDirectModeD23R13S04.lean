import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD23R13
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R13G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R13G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R13G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R13G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R13G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R13G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 23 23 13)=sourceGroupEndD23R13G05S04 := by
  change foldNormalBlocks sourceGroupStartD23R13G00S04 ([sourceBlock 23 23 13 0,sourceBlock 23 23 13 1,sourceBlock 23 23 13 2,sourceBlock 23 23 13 3] ++ ([sourceBlock 23 23 13 4,sourceBlock 23 23 13 5,sourceBlock 23 23 13 6,sourceBlock 23 23 13 7] ++ ([sourceBlock 23 23 13 8,sourceBlock 23 23 13 9,sourceBlock 23 23 13 10,sourceBlock 23 23 13 11] ++ ([sourceBlock 23 23 13 12,sourceBlock 23 23 13 13,sourceBlock 23 23 13 14,sourceBlock 23 23 13 15] ++ ([sourceBlock 23 23 13 16,sourceBlock 23 23 13 17,sourceBlock 23 23 13 18,sourceBlock 23 23 13 19] ++ ([sourceBlock 23 23 13 20,sourceBlock 23 23 13 21,sourceBlock 23 23 13 22,sourceBlock 23 23 13 23]))))))=sourceGroupEndD23R13G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD23R13G00S04]
  have boundary00 : sourceGroupEndD23R13G00S04 =
      sourceGroupStartD23R13G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R13G01S04]
  have boundary01 : sourceGroupEndD23R13G01S04 =
      sourceGroupStartD23R13G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R13G02S04]
  have boundary02 : sourceGroupEndD23R13G02S04 =
      sourceGroupStartD23R13G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R13G03S04]
  have boundary03 : sourceGroupEndD23R13G03S04 =
      sourceGroupStartD23R13G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R13G04S04]
  have boundary04 : sourceGroupEndD23R13G04S04 =
      sourceGroupStartD23R13G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD23R13G05S04

theorem sourceDirectCheckD23R13 :
    alternateIntegerFourWords (integerSourceWords 23 23 13)=
      alternateIntegerFourWords (integerSlaterWords 23 13) := by
  apply originalSlaterMode_of_blocks_check 23 13 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD23R13,slaterNormalCheckD23R13]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD23R13
