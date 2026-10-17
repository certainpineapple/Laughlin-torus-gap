import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD21R09
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R09G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R09G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R09G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R09G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R09G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R09G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 21 21 9)=sourceGroupEndD21R09G05S04 := by
  change foldNormalBlocks sourceGroupStartD21R09G00S04 ([sourceBlock 21 21 9 0,sourceBlock 21 21 9 1,sourceBlock 21 21 9 2,sourceBlock 21 21 9 3] ++ ([sourceBlock 21 21 9 4,sourceBlock 21 21 9 5,sourceBlock 21 21 9 6,sourceBlock 21 21 9 7] ++ ([sourceBlock 21 21 9 8,sourceBlock 21 21 9 9,sourceBlock 21 21 9 10,sourceBlock 21 21 9 11] ++ ([sourceBlock 21 21 9 12,sourceBlock 21 21 9 13,sourceBlock 21 21 9 14,sourceBlock 21 21 9 15] ++ ([sourceBlock 21 21 9 16,sourceBlock 21 21 9 17,sourceBlock 21 21 9 18,sourceBlock 21 21 9 19] ++ ([sourceBlock 21 21 9 20,sourceBlock 21 21 9 21]))))))=sourceGroupEndD21R09G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD21R09G00S04]
  have boundary00 : sourceGroupEndD21R09G00S04 =
      sourceGroupStartD21R09G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD21R09G01S04]
  have boundary01 : sourceGroupEndD21R09G01S04 =
      sourceGroupStartD21R09G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD21R09G02S04]
  have boundary02 : sourceGroupEndD21R09G02S04 =
      sourceGroupStartD21R09G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD21R09G03S04]
  have boundary03 : sourceGroupEndD21R09G03S04 =
      sourceGroupStartD21R09G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD21R09G04S04]
  have boundary04 : sourceGroupEndD21R09G04S04 =
      sourceGroupStartD21R09G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD21R09G05S04

theorem sourceDirectCheckD21R09 :
    alternateIntegerFourWords (integerSourceWords 21 21 9)=
      alternateIntegerFourWords (integerSlaterWords 21 9) := by
  apply originalSlaterMode_of_blocks_check 21 9 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD21R09,slaterNormalCheckD21R09]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD21R09
