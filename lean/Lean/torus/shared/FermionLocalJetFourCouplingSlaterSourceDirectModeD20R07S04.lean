import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD20R07
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R07G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R07G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R07G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R07G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R07G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R07G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 20 20 7)=sourceGroupEndD20R07G05S04 := by
  change foldNormalBlocks sourceGroupStartD20R07G00S04 ([sourceBlock 20 20 7 0,sourceBlock 20 20 7 1,sourceBlock 20 20 7 2,sourceBlock 20 20 7 3] ++ ([sourceBlock 20 20 7 4,sourceBlock 20 20 7 5,sourceBlock 20 20 7 6,sourceBlock 20 20 7 7] ++ ([sourceBlock 20 20 7 8,sourceBlock 20 20 7 9,sourceBlock 20 20 7 10,sourceBlock 20 20 7 11] ++ ([sourceBlock 20 20 7 12,sourceBlock 20 20 7 13,sourceBlock 20 20 7 14,sourceBlock 20 20 7 15] ++ ([sourceBlock 20 20 7 16,sourceBlock 20 20 7 17,sourceBlock 20 20 7 18,sourceBlock 20 20 7 19] ++ ([sourceBlock 20 20 7 20]))))))=sourceGroupEndD20R07G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD20R07G00S04]
  have boundary00 : sourceGroupEndD20R07G00S04 =
      sourceGroupStartD20R07G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD20R07G01S04]
  have boundary01 : sourceGroupEndD20R07G01S04 =
      sourceGroupStartD20R07G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD20R07G02S04]
  have boundary02 : sourceGroupEndD20R07G02S04 =
      sourceGroupStartD20R07G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD20R07G03S04]
  have boundary03 : sourceGroupEndD20R07G03S04 =
      sourceGroupStartD20R07G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD20R07G04S04]
  have boundary04 : sourceGroupEndD20R07G04S04 =
      sourceGroupStartD20R07G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD20R07G05S04

theorem sourceDirectCheckD20R07 :
    alternateIntegerFourWords (integerSourceWords 20 20 7)=
      alternateIntegerFourWords (integerSlaterWords 20 7) := by
  apply originalSlaterMode_of_blocks_check 20 7 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD20R07,slaterNormalCheckD20R07]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD20R07
