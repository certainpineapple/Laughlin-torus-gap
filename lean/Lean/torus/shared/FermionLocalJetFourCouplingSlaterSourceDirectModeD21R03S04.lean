import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD21R03
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R03G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R03G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R03G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R03G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R03G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R03G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 21 21 3)=sourceGroupEndD21R03G05S04 := by
  change foldNormalBlocks sourceGroupStartD21R03G00S04 ([sourceBlock 21 21 3 0,sourceBlock 21 21 3 1,sourceBlock 21 21 3 2,sourceBlock 21 21 3 3] ++ ([sourceBlock 21 21 3 4,sourceBlock 21 21 3 5,sourceBlock 21 21 3 6,sourceBlock 21 21 3 7] ++ ([sourceBlock 21 21 3 8,sourceBlock 21 21 3 9,sourceBlock 21 21 3 10,sourceBlock 21 21 3 11] ++ ([sourceBlock 21 21 3 12,sourceBlock 21 21 3 13,sourceBlock 21 21 3 14,sourceBlock 21 21 3 15] ++ ([sourceBlock 21 21 3 16,sourceBlock 21 21 3 17,sourceBlock 21 21 3 18,sourceBlock 21 21 3 19] ++ ([sourceBlock 21 21 3 20,sourceBlock 21 21 3 21]))))))=sourceGroupEndD21R03G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD21R03G00S04]
  have boundary00 : sourceGroupEndD21R03G00S04 =
      sourceGroupStartD21R03G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD21R03G01S04]
  have boundary01 : sourceGroupEndD21R03G01S04 =
      sourceGroupStartD21R03G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD21R03G02S04]
  have boundary02 : sourceGroupEndD21R03G02S04 =
      sourceGroupStartD21R03G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD21R03G03S04]
  have boundary03 : sourceGroupEndD21R03G03S04 =
      sourceGroupStartD21R03G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD21R03G04S04]
  have boundary04 : sourceGroupEndD21R03G04S04 =
      sourceGroupStartD21R03G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD21R03G05S04

theorem sourceDirectCheckD21R03 :
    alternateIntegerFourWords (integerSourceWords 21 21 3)=
      alternateIntegerFourWords (integerSlaterWords 21 3) := by
  apply originalSlaterMode_of_blocks_check 21 3 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD21R03,slaterNormalCheckD21R03]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD21R03
