import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD23R15
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R15G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R15G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R15G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R15G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R15G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R15G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 23 23 15)=sourceGroupEndD23R15G05S04 := by
  change foldNormalBlocks sourceGroupStartD23R15G00S04 ([sourceBlock 23 23 15 0,sourceBlock 23 23 15 1,sourceBlock 23 23 15 2,sourceBlock 23 23 15 3] ++ ([sourceBlock 23 23 15 4,sourceBlock 23 23 15 5,sourceBlock 23 23 15 6,sourceBlock 23 23 15 7] ++ ([sourceBlock 23 23 15 8,sourceBlock 23 23 15 9,sourceBlock 23 23 15 10,sourceBlock 23 23 15 11] ++ ([sourceBlock 23 23 15 12,sourceBlock 23 23 15 13,sourceBlock 23 23 15 14,sourceBlock 23 23 15 15] ++ ([sourceBlock 23 23 15 16,sourceBlock 23 23 15 17,sourceBlock 23 23 15 18,sourceBlock 23 23 15 19] ++ ([sourceBlock 23 23 15 20,sourceBlock 23 23 15 21,sourceBlock 23 23 15 22,sourceBlock 23 23 15 23]))))))=sourceGroupEndD23R15G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD23R15G00S04]
  have boundary00 : sourceGroupEndD23R15G00S04 =
      sourceGroupStartD23R15G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R15G01S04]
  have boundary01 : sourceGroupEndD23R15G01S04 =
      sourceGroupStartD23R15G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R15G02S04]
  have boundary02 : sourceGroupEndD23R15G02S04 =
      sourceGroupStartD23R15G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R15G03S04]
  have boundary03 : sourceGroupEndD23R15G03S04 =
      sourceGroupStartD23R15G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R15G04S04]
  have boundary04 : sourceGroupEndD23R15G04S04 =
      sourceGroupStartD23R15G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD23R15G05S04

theorem sourceDirectCheckD23R15 :
    alternateIntegerFourWords (integerSourceWords 23 23 15)=
      alternateIntegerFourWords (integerSlaterWords 23 15) := by
  apply originalSlaterMode_of_blocks_check 23 15 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD23R15,slaterNormalCheckD23R15]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD23R15
