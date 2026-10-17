import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD21R01
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R01G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R01G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R01G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R01G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R01G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R01G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 21 21 1)=sourceGroupEndD21R01G05S04 := by
  change foldNormalBlocks sourceGroupStartD21R01G00S04 ([sourceBlock 21 21 1 0,sourceBlock 21 21 1 1,sourceBlock 21 21 1 2,sourceBlock 21 21 1 3] ++ ([sourceBlock 21 21 1 4,sourceBlock 21 21 1 5,sourceBlock 21 21 1 6,sourceBlock 21 21 1 7] ++ ([sourceBlock 21 21 1 8,sourceBlock 21 21 1 9,sourceBlock 21 21 1 10,sourceBlock 21 21 1 11] ++ ([sourceBlock 21 21 1 12,sourceBlock 21 21 1 13,sourceBlock 21 21 1 14,sourceBlock 21 21 1 15] ++ ([sourceBlock 21 21 1 16,sourceBlock 21 21 1 17,sourceBlock 21 21 1 18,sourceBlock 21 21 1 19] ++ ([sourceBlock 21 21 1 20,sourceBlock 21 21 1 21]))))))=sourceGroupEndD21R01G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD21R01G00S04]
  have boundary00 : sourceGroupEndD21R01G00S04 =
      sourceGroupStartD21R01G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD21R01G01S04]
  have boundary01 : sourceGroupEndD21R01G01S04 =
      sourceGroupStartD21R01G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD21R01G02S04]
  have boundary02 : sourceGroupEndD21R01G02S04 =
      sourceGroupStartD21R01G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD21R01G03S04]
  have boundary03 : sourceGroupEndD21R01G03S04 =
      sourceGroupStartD21R01G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD21R01G04S04]
  have boundary04 : sourceGroupEndD21R01G04S04 =
      sourceGroupStartD21R01G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD21R01G05S04

theorem sourceDirectCheckD21R01 :
    alternateIntegerFourWords (integerSourceWords 21 21 1)=
      alternateIntegerFourWords (integerSlaterWords 21 1) := by
  apply originalSlaterMode_of_blocks_check 21 1 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD21R01,slaterNormalCheckD21R01]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD21R01
