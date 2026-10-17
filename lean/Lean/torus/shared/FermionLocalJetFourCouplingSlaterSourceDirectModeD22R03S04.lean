import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD22R03
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R03G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R03G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R03G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R03G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R03G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R03G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 22 22 3)=sourceGroupEndD22R03G05S04 := by
  change foldNormalBlocks sourceGroupStartD22R03G00S04 ([sourceBlock 22 22 3 0,sourceBlock 22 22 3 1,sourceBlock 22 22 3 2,sourceBlock 22 22 3 3] ++ ([sourceBlock 22 22 3 4,sourceBlock 22 22 3 5,sourceBlock 22 22 3 6,sourceBlock 22 22 3 7] ++ ([sourceBlock 22 22 3 8,sourceBlock 22 22 3 9,sourceBlock 22 22 3 10,sourceBlock 22 22 3 11] ++ ([sourceBlock 22 22 3 12,sourceBlock 22 22 3 13,sourceBlock 22 22 3 14,sourceBlock 22 22 3 15] ++ ([sourceBlock 22 22 3 16,sourceBlock 22 22 3 17,sourceBlock 22 22 3 18,sourceBlock 22 22 3 19] ++ ([sourceBlock 22 22 3 20,sourceBlock 22 22 3 21,sourceBlock 22 22 3 22]))))))=sourceGroupEndD22R03G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD22R03G00S04]
  have boundary00 : sourceGroupEndD22R03G00S04 =
      sourceGroupStartD22R03G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R03G01S04]
  have boundary01 : sourceGroupEndD22R03G01S04 =
      sourceGroupStartD22R03G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R03G02S04]
  have boundary02 : sourceGroupEndD22R03G02S04 =
      sourceGroupStartD22R03G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R03G03S04]
  have boundary03 : sourceGroupEndD22R03G03S04 =
      sourceGroupStartD22R03G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R03G04S04]
  have boundary04 : sourceGroupEndD22R03G04S04 =
      sourceGroupStartD22R03G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD22R03G05S04

theorem sourceDirectCheckD22R03 :
    alternateIntegerFourWords (integerSourceWords 22 22 3)=
      alternateIntegerFourWords (integerSlaterWords 22 3) := by
  apply originalSlaterMode_of_blocks_check 22 3 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD22R03,slaterNormalCheckD22R03]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD22R03
