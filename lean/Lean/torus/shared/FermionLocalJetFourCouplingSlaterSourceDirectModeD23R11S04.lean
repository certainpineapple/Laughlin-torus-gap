import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD23R11
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R11G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R11G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R11G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R11G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R11G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R11G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 23 23 11)=sourceGroupEndD23R11G05S04 := by
  change foldNormalBlocks sourceGroupStartD23R11G00S04 ([sourceBlock 23 23 11 0,sourceBlock 23 23 11 1,sourceBlock 23 23 11 2,sourceBlock 23 23 11 3] ++ ([sourceBlock 23 23 11 4,sourceBlock 23 23 11 5,sourceBlock 23 23 11 6,sourceBlock 23 23 11 7] ++ ([sourceBlock 23 23 11 8,sourceBlock 23 23 11 9,sourceBlock 23 23 11 10,sourceBlock 23 23 11 11] ++ ([sourceBlock 23 23 11 12,sourceBlock 23 23 11 13,sourceBlock 23 23 11 14,sourceBlock 23 23 11 15] ++ ([sourceBlock 23 23 11 16,sourceBlock 23 23 11 17,sourceBlock 23 23 11 18,sourceBlock 23 23 11 19] ++ ([sourceBlock 23 23 11 20,sourceBlock 23 23 11 21,sourceBlock 23 23 11 22,sourceBlock 23 23 11 23]))))))=sourceGroupEndD23R11G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD23R11G00S04]
  have boundary00 : sourceGroupEndD23R11G00S04 =
      sourceGroupStartD23R11G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R11G01S04]
  have boundary01 : sourceGroupEndD23R11G01S04 =
      sourceGroupStartD23R11G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R11G02S04]
  have boundary02 : sourceGroupEndD23R11G02S04 =
      sourceGroupStartD23R11G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R11G03S04]
  have boundary03 : sourceGroupEndD23R11G03S04 =
      sourceGroupStartD23R11G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R11G04S04]
  have boundary04 : sourceGroupEndD23R11G04S04 =
      sourceGroupStartD23R11G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD23R11G05S04

theorem sourceDirectCheckD23R11 :
    alternateIntegerFourWords (integerSourceWords 23 23 11)=
      alternateIntegerFourWords (integerSlaterWords 23 11) := by
  apply originalSlaterMode_of_blocks_check 23 11 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD23R11,slaterNormalCheckD23R11]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD23R11
