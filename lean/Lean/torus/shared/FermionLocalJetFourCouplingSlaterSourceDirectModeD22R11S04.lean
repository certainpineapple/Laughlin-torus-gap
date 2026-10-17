import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD22R11
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R11G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R11G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R11G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R11G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R11G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD22R11G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 22 22 11)=sourceGroupEndD22R11G05S04 := by
  change foldNormalBlocks sourceGroupStartD22R11G00S04 ([sourceBlock 22 22 11 0,sourceBlock 22 22 11 1,sourceBlock 22 22 11 2,sourceBlock 22 22 11 3] ++ ([sourceBlock 22 22 11 4,sourceBlock 22 22 11 5,sourceBlock 22 22 11 6,sourceBlock 22 22 11 7] ++ ([sourceBlock 22 22 11 8,sourceBlock 22 22 11 9,sourceBlock 22 22 11 10,sourceBlock 22 22 11 11] ++ ([sourceBlock 22 22 11 12,sourceBlock 22 22 11 13,sourceBlock 22 22 11 14,sourceBlock 22 22 11 15] ++ ([sourceBlock 22 22 11 16,sourceBlock 22 22 11 17,sourceBlock 22 22 11 18,sourceBlock 22 22 11 19] ++ ([sourceBlock 22 22 11 20,sourceBlock 22 22 11 21,sourceBlock 22 22 11 22]))))))=sourceGroupEndD22R11G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD22R11G00S04]
  have boundary00 : sourceGroupEndD22R11G00S04 =
      sourceGroupStartD22R11G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R11G01S04]
  have boundary01 : sourceGroupEndD22R11G01S04 =
      sourceGroupStartD22R11G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R11G02S04]
  have boundary02 : sourceGroupEndD22R11G02S04 =
      sourceGroupStartD22R11G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R11G03S04]
  have boundary03 : sourceGroupEndD22R11G03S04 =
      sourceGroupStartD22R11G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD22R11G04S04]
  have boundary04 : sourceGroupEndD22R11G04S04 =
      sourceGroupStartD22R11G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD22R11G05S04

theorem sourceDirectCheckD22R11 :
    alternateIntegerFourWords (integerSourceWords 22 22 11)=
      alternateIntegerFourWords (integerSlaterWords 22 11) := by
  apply originalSlaterMode_of_blocks_check 22 11 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD22R11,slaterNormalCheckD22R11]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD22R11
