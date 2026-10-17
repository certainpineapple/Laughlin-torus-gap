import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD23R03
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R03G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R03G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R03G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R03G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R03G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R03G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 23 23 3)=sourceGroupEndD23R03G05S04 := by
  change foldNormalBlocks sourceGroupStartD23R03G00S04 ([sourceBlock 23 23 3 0,sourceBlock 23 23 3 1,sourceBlock 23 23 3 2,sourceBlock 23 23 3 3] ++ ([sourceBlock 23 23 3 4,sourceBlock 23 23 3 5,sourceBlock 23 23 3 6,sourceBlock 23 23 3 7] ++ ([sourceBlock 23 23 3 8,sourceBlock 23 23 3 9,sourceBlock 23 23 3 10,sourceBlock 23 23 3 11] ++ ([sourceBlock 23 23 3 12,sourceBlock 23 23 3 13,sourceBlock 23 23 3 14,sourceBlock 23 23 3 15] ++ ([sourceBlock 23 23 3 16,sourceBlock 23 23 3 17,sourceBlock 23 23 3 18,sourceBlock 23 23 3 19] ++ ([sourceBlock 23 23 3 20,sourceBlock 23 23 3 21,sourceBlock 23 23 3 22,sourceBlock 23 23 3 23]))))))=sourceGroupEndD23R03G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD23R03G00S04]
  have boundary00 : sourceGroupEndD23R03G00S04 =
      sourceGroupStartD23R03G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R03G01S04]
  have boundary01 : sourceGroupEndD23R03G01S04 =
      sourceGroupStartD23R03G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R03G02S04]
  have boundary02 : sourceGroupEndD23R03G02S04 =
      sourceGroupStartD23R03G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R03G03S04]
  have boundary03 : sourceGroupEndD23R03G03S04 =
      sourceGroupStartD23R03G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R03G04S04]
  have boundary04 : sourceGroupEndD23R03G04S04 =
      sourceGroupStartD23R03G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD23R03G05S04

theorem sourceDirectCheckD23R03 :
    alternateIntegerFourWords (integerSourceWords 23 23 3)=
      alternateIntegerFourWords (integerSlaterWords 23 3) := by
  apply originalSlaterMode_of_blocks_check 23 3 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD23R03,slaterNormalCheckD23R03]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD23R03
