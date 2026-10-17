import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD22R05
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R05G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R05G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R05G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R05G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R05G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R05G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 22 22 5)=sourceGroupEndD22R05G05S04 := by
  change foldNormalBlocks sourceGroupStartD22R05G00S04 ([sourceBlock 22 22 5 0,sourceBlock 22 22 5 1,sourceBlock 22 22 5 2,sourceBlock 22 22 5 3] ++ ([sourceBlock 22 22 5 4,sourceBlock 22 22 5 5,sourceBlock 22 22 5 6,sourceBlock 22 22 5 7] ++ ([sourceBlock 22 22 5 8,sourceBlock 22 22 5 9,sourceBlock 22 22 5 10,sourceBlock 22 22 5 11] ++ ([sourceBlock 22 22 5 12,sourceBlock 22 22 5 13,sourceBlock 22 22 5 14,sourceBlock 22 22 5 15] ++ ([sourceBlock 22 22 5 16,sourceBlock 22 22 5 17,sourceBlock 22 22 5 18,sourceBlock 22 22 5 19] ++ ([sourceBlock 22 22 5 20,sourceBlock 22 22 5 21,sourceBlock 22 22 5 22]))))))=sourceGroupEndD22R05G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD22R05G00S04]
  have boundary00 : sourceGroupEndD22R05G00S04 =
      sourceGroupStartD22R05G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R05G01S04]
  have boundary01 : sourceGroupEndD22R05G01S04 =
      sourceGroupStartD22R05G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R05G02S04]
  have boundary02 : sourceGroupEndD22R05G02S04 =
      sourceGroupStartD22R05G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R05G03S04]
  have boundary03 : sourceGroupEndD22R05G03S04 =
      sourceGroupStartD22R05G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R05G04S04]
  have boundary04 : sourceGroupEndD22R05G04S04 =
      sourceGroupStartD22R05G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD22R05G05S04

theorem sourceDirectCheckD22R05 :
    alternateIntegerFourWords (integerSourceWords 22 22 5)=
      alternateIntegerFourWords (integerSlaterWords 22 5) := by
  apply originalSlaterMode_of_blocks_check 22 5 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD22R05,slaterNormalCheckD22R05]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD22R05
