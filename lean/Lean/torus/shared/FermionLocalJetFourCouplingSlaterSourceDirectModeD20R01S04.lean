import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD20R01
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R01G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R01G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R01G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R01G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R01G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R01G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 20 20 1)=sourceGroupEndD20R01G05S04 := by
  change foldNormalBlocks sourceGroupStartD20R01G00S04 ([sourceBlock 20 20 1 0,sourceBlock 20 20 1 1,sourceBlock 20 20 1 2,sourceBlock 20 20 1 3] ++ ([sourceBlock 20 20 1 4,sourceBlock 20 20 1 5,sourceBlock 20 20 1 6,sourceBlock 20 20 1 7] ++ ([sourceBlock 20 20 1 8,sourceBlock 20 20 1 9,sourceBlock 20 20 1 10,sourceBlock 20 20 1 11] ++ ([sourceBlock 20 20 1 12,sourceBlock 20 20 1 13,sourceBlock 20 20 1 14,sourceBlock 20 20 1 15] ++ ([sourceBlock 20 20 1 16,sourceBlock 20 20 1 17,sourceBlock 20 20 1 18,sourceBlock 20 20 1 19] ++ ([sourceBlock 20 20 1 20]))))))=sourceGroupEndD20R01G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD20R01G00S04]
  have boundary00 : sourceGroupEndD20R01G00S04 =
      sourceGroupStartD20R01G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD20R01G01S04]
  have boundary01 : sourceGroupEndD20R01G01S04 =
      sourceGroupStartD20R01G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD20R01G02S04]
  have boundary02 : sourceGroupEndD20R01G02S04 =
      sourceGroupStartD20R01G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD20R01G03S04]
  have boundary03 : sourceGroupEndD20R01G03S04 =
      sourceGroupStartD20R01G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD20R01G04S04]
  have boundary04 : sourceGroupEndD20R01G04S04 =
      sourceGroupStartD20R01G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD20R01G05S04

theorem sourceDirectCheckD20R01 :
    alternateIntegerFourWords (integerSourceWords 20 20 1)=
      alternateIntegerFourWords (integerSlaterWords 20 1) := by
  apply originalSlaterMode_of_blocks_check 20 1 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD20R01,slaterNormalCheckD20R01]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD20R01
