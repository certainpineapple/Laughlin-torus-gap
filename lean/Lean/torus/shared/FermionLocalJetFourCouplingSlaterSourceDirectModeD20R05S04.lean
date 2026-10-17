import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD20R05
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R05G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R05G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R05G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R05G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R05G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R05G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 20 20 5)=sourceGroupEndD20R05G05S04 := by
  change foldNormalBlocks sourceGroupStartD20R05G00S04 ([sourceBlock 20 20 5 0,sourceBlock 20 20 5 1,sourceBlock 20 20 5 2,sourceBlock 20 20 5 3] ++ ([sourceBlock 20 20 5 4,sourceBlock 20 20 5 5,sourceBlock 20 20 5 6,sourceBlock 20 20 5 7] ++ ([sourceBlock 20 20 5 8,sourceBlock 20 20 5 9,sourceBlock 20 20 5 10,sourceBlock 20 20 5 11] ++ ([sourceBlock 20 20 5 12,sourceBlock 20 20 5 13,sourceBlock 20 20 5 14,sourceBlock 20 20 5 15] ++ ([sourceBlock 20 20 5 16,sourceBlock 20 20 5 17,sourceBlock 20 20 5 18,sourceBlock 20 20 5 19] ++ ([sourceBlock 20 20 5 20]))))))=sourceGroupEndD20R05G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD20R05G00S04]
  have boundary00 : sourceGroupEndD20R05G00S04 =
      sourceGroupStartD20R05G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD20R05G01S04]
  have boundary01 : sourceGroupEndD20R05G01S04 =
      sourceGroupStartD20R05G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD20R05G02S04]
  have boundary02 : sourceGroupEndD20R05G02S04 =
      sourceGroupStartD20R05G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD20R05G03S04]
  have boundary03 : sourceGroupEndD20R05G03S04 =
      sourceGroupStartD20R05G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD20R05G04S04]
  have boundary04 : sourceGroupEndD20R05G04S04 =
      sourceGroupStartD20R05G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD20R05G05S04

theorem sourceDirectCheckD20R05 :
    alternateIntegerFourWords (integerSourceWords 20 20 5)=
      alternateIntegerFourWords (integerSlaterWords 20 5) := by
  apply originalSlaterMode_of_blocks_check 20 5 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD20R05,slaterNormalCheckD20R05]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD20R05
