import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD22R07
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R07G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R07G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R07G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R07G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R07G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R07G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 22 22 7)=sourceGroupEndD22R07G05S04 := by
  change foldNormalBlocks sourceGroupStartD22R07G00S04 ([sourceBlock 22 22 7 0,sourceBlock 22 22 7 1,sourceBlock 22 22 7 2,sourceBlock 22 22 7 3] ++ ([sourceBlock 22 22 7 4,sourceBlock 22 22 7 5,sourceBlock 22 22 7 6,sourceBlock 22 22 7 7] ++ ([sourceBlock 22 22 7 8,sourceBlock 22 22 7 9,sourceBlock 22 22 7 10,sourceBlock 22 22 7 11] ++ ([sourceBlock 22 22 7 12,sourceBlock 22 22 7 13,sourceBlock 22 22 7 14,sourceBlock 22 22 7 15] ++ ([sourceBlock 22 22 7 16,sourceBlock 22 22 7 17,sourceBlock 22 22 7 18,sourceBlock 22 22 7 19] ++ ([sourceBlock 22 22 7 20,sourceBlock 22 22 7 21,sourceBlock 22 22 7 22]))))))=sourceGroupEndD22R07G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD22R07G00S04]
  have boundary00 : sourceGroupEndD22R07G00S04 =
      sourceGroupStartD22R07G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R07G01S04]
  have boundary01 : sourceGroupEndD22R07G01S04 =
      sourceGroupStartD22R07G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R07G02S04]
  have boundary02 : sourceGroupEndD22R07G02S04 =
      sourceGroupStartD22R07G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R07G03S04]
  have boundary03 : sourceGroupEndD22R07G03S04 =
      sourceGroupStartD22R07G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R07G04S04]
  have boundary04 : sourceGroupEndD22R07G04S04 =
      sourceGroupStartD22R07G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD22R07G05S04

theorem sourceDirectCheckD22R07 :
    alternateIntegerFourWords (integerSourceWords 22 22 7)=
      alternateIntegerFourWords (integerSlaterWords 22 7) := by
  apply originalSlaterMode_of_blocks_check 22 7 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD22R07,slaterNormalCheckD22R07]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD22R07
