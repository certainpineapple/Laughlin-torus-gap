import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD23R07
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R07G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R07G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R07G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R07G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R07G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R07G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 23 23 7)=sourceGroupEndD23R07G05S04 := by
  change foldNormalBlocks sourceGroupStartD23R07G00S04 ([sourceBlock 23 23 7 0,sourceBlock 23 23 7 1,sourceBlock 23 23 7 2,sourceBlock 23 23 7 3] ++ ([sourceBlock 23 23 7 4,sourceBlock 23 23 7 5,sourceBlock 23 23 7 6,sourceBlock 23 23 7 7] ++ ([sourceBlock 23 23 7 8,sourceBlock 23 23 7 9,sourceBlock 23 23 7 10,sourceBlock 23 23 7 11] ++ ([sourceBlock 23 23 7 12,sourceBlock 23 23 7 13,sourceBlock 23 23 7 14,sourceBlock 23 23 7 15] ++ ([sourceBlock 23 23 7 16,sourceBlock 23 23 7 17,sourceBlock 23 23 7 18,sourceBlock 23 23 7 19] ++ ([sourceBlock 23 23 7 20,sourceBlock 23 23 7 21,sourceBlock 23 23 7 22,sourceBlock 23 23 7 23]))))))=sourceGroupEndD23R07G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD23R07G00S04]
  have boundary00 : sourceGroupEndD23R07G00S04 =
      sourceGroupStartD23R07G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R07G01S04]
  have boundary01 : sourceGroupEndD23R07G01S04 =
      sourceGroupStartD23R07G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R07G02S04]
  have boundary02 : sourceGroupEndD23R07G02S04 =
      sourceGroupStartD23R07G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R07G03S04]
  have boundary03 : sourceGroupEndD23R07G03S04 =
      sourceGroupStartD23R07G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R07G04S04]
  have boundary04 : sourceGroupEndD23R07G04S04 =
      sourceGroupStartD23R07G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD23R07G05S04

theorem sourceDirectCheckD23R07 :
    alternateIntegerFourWords (integerSourceWords 23 23 7)=
      alternateIntegerFourWords (integerSlaterWords 23 7) := by
  apply originalSlaterMode_of_blocks_check 23 7 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD23R07,slaterNormalCheckD23R07]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD23R07
