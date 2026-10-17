import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD21R07
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R07G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R07G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R07G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R07G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R07G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R07G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 21 21 7)=sourceGroupEndD21R07G05S04 := by
  change foldNormalBlocks sourceGroupStartD21R07G00S04 ([sourceBlock 21 21 7 0,sourceBlock 21 21 7 1,sourceBlock 21 21 7 2,sourceBlock 21 21 7 3] ++ ([sourceBlock 21 21 7 4,sourceBlock 21 21 7 5,sourceBlock 21 21 7 6,sourceBlock 21 21 7 7] ++ ([sourceBlock 21 21 7 8,sourceBlock 21 21 7 9,sourceBlock 21 21 7 10,sourceBlock 21 21 7 11] ++ ([sourceBlock 21 21 7 12,sourceBlock 21 21 7 13,sourceBlock 21 21 7 14,sourceBlock 21 21 7 15] ++ ([sourceBlock 21 21 7 16,sourceBlock 21 21 7 17,sourceBlock 21 21 7 18,sourceBlock 21 21 7 19] ++ ([sourceBlock 21 21 7 20,sourceBlock 21 21 7 21]))))))=sourceGroupEndD21R07G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD21R07G00S04]
  have boundary00 : sourceGroupEndD21R07G00S04 =
      sourceGroupStartD21R07G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD21R07G01S04]
  have boundary01 : sourceGroupEndD21R07G01S04 =
      sourceGroupStartD21R07G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD21R07G02S04]
  have boundary02 : sourceGroupEndD21R07G02S04 =
      sourceGroupStartD21R07G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD21R07G03S04]
  have boundary03 : sourceGroupEndD21R07G03S04 =
      sourceGroupStartD21R07G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD21R07G04S04]
  have boundary04 : sourceGroupEndD21R07G04S04 =
      sourceGroupStartD21R07G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD21R07G05S04

theorem sourceDirectCheckD21R07 :
    alternateIntegerFourWords (integerSourceWords 21 21 7)=
      alternateIntegerFourWords (integerSlaterWords 21 7) := by
  apply originalSlaterMode_of_blocks_check 21 7 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD21R07,slaterNormalCheckD21R07]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD21R07
