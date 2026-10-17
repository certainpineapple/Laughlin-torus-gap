import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD23R01
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R01G00S02
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R01G01S02
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R01G02S02
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R01G03S02
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R01G04S02
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R01G05S02
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R01G06S02
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R01G07S02
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R01G08S02
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R01G09S02
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R01G10S02
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD23R01G11S02

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 23 23 1)=sourceGroupEndD23R01G11S02 := by
  change foldNormalBlocks sourceGroupStartD23R01G00S02 ([sourceBlock 23 23 1 0,sourceBlock 23 23 1 1] ++ ([sourceBlock 23 23 1 2,sourceBlock 23 23 1 3] ++ ([sourceBlock 23 23 1 4,sourceBlock 23 23 1 5] ++ ([sourceBlock 23 23 1 6,sourceBlock 23 23 1 7] ++ ([sourceBlock 23 23 1 8,sourceBlock 23 23 1 9] ++ ([sourceBlock 23 23 1 10,sourceBlock 23 23 1 11] ++ ([sourceBlock 23 23 1 12,sourceBlock 23 23 1 13] ++ ([sourceBlock 23 23 1 14,sourceBlock 23 23 1 15] ++ ([sourceBlock 23 23 1 16,sourceBlock 23 23 1 17] ++ ([sourceBlock 23 23 1 18,sourceBlock 23 23 1 19] ++ ([sourceBlock 23 23 1 20,sourceBlock 23 23 1 21] ++ ([sourceBlock 23 23 1 22,sourceBlock 23 23 1 23]))))))))))))=sourceGroupEndD23R01G11S02
  rw [foldNormalBlocks_append,sourceGroupCheckD23R01G00S02]
  have boundary00 : sourceGroupEndD23R01G00S02 =
      sourceGroupStartD23R01G01S02 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R01G01S02]
  have boundary01 : sourceGroupEndD23R01G01S02 =
      sourceGroupStartD23R01G02S02 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R01G02S02]
  have boundary02 : sourceGroupEndD23R01G02S02 =
      sourceGroupStartD23R01G03S02 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R01G03S02]
  have boundary03 : sourceGroupEndD23R01G03S02 =
      sourceGroupStartD23R01G04S02 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R01G04S02]
  have boundary04 : sourceGroupEndD23R01G04S02 =
      sourceGroupStartD23R01G05S02 := by rfl
  rw [boundary04]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R01G05S02]
  have boundary05 : sourceGroupEndD23R01G05S02 =
      sourceGroupStartD23R01G06S02 := by rfl
  rw [boundary05]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R01G06S02]
  have boundary06 : sourceGroupEndD23R01G06S02 =
      sourceGroupStartD23R01G07S02 := by rfl
  rw [boundary06]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R01G07S02]
  have boundary07 : sourceGroupEndD23R01G07S02 =
      sourceGroupStartD23R01G08S02 := by rfl
  rw [boundary07]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R01G08S02]
  have boundary08 : sourceGroupEndD23R01G08S02 =
      sourceGroupStartD23R01G09S02 := by rfl
  rw [boundary08]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R01G09S02]
  have boundary09 : sourceGroupEndD23R01G09S02 =
      sourceGroupStartD23R01G10S02 := by rfl
  rw [boundary09]
  rw [foldNormalBlocks_append,sourceGroupCheckD23R01G10S02]
  have boundary10 : sourceGroupEndD23R01G10S02 =
      sourceGroupStartD23R01G11S02 := by rfl
  rw [boundary10]
  exact sourceGroupCheckD23R01G11S02

theorem sourceDirectCheckD23R01 :
    alternateIntegerFourWords (integerSourceWords 23 23 1)=
      alternateIntegerFourWords (integerSlaterWords 23 1) := by
  apply originalSlaterMode_of_blocks_check 23 1 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD23R01,slaterNormalCheckD23R01]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD23R01
