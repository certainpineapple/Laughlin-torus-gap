import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD20R03
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R03G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R03G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R03G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R03G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R03G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD20R03G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 20 20 3)=sourceGroupEndD20R03G05S04 := by
  change foldNormalBlocks sourceGroupStartD20R03G00S04 ([sourceBlock 20 20 3 0,sourceBlock 20 20 3 1,sourceBlock 20 20 3 2,sourceBlock 20 20 3 3] ++ ([sourceBlock 20 20 3 4,sourceBlock 20 20 3 5,sourceBlock 20 20 3 6,sourceBlock 20 20 3 7] ++ ([sourceBlock 20 20 3 8,sourceBlock 20 20 3 9,sourceBlock 20 20 3 10,sourceBlock 20 20 3 11] ++ ([sourceBlock 20 20 3 12,sourceBlock 20 20 3 13,sourceBlock 20 20 3 14,sourceBlock 20 20 3 15] ++ ([sourceBlock 20 20 3 16,sourceBlock 20 20 3 17,sourceBlock 20 20 3 18,sourceBlock 20 20 3 19] ++ ([sourceBlock 20 20 3 20]))))))=sourceGroupEndD20R03G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD20R03G00S04]
  have boundary00 : sourceGroupEndD20R03G00S04 =
      sourceGroupStartD20R03G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD20R03G01S04]
  have boundary01 : sourceGroupEndD20R03G01S04 =
      sourceGroupStartD20R03G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD20R03G02S04]
  have boundary02 : sourceGroupEndD20R03G02S04 =
      sourceGroupStartD20R03G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD20R03G03S04]
  have boundary03 : sourceGroupEndD20R03G03S04 =
      sourceGroupStartD20R03G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD20R03G04S04]
  have boundary04 : sourceGroupEndD20R03G04S04 =
      sourceGroupStartD20R03G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD20R03G05S04

theorem sourceDirectCheckD20R03 :
    alternateIntegerFourWords (integerSourceWords 20 20 3)=
      alternateIntegerFourWords (integerSlaterWords 20 3) := by
  apply originalSlaterMode_of_blocks_check 20 3 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD20R03,slaterNormalCheckD20R03]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD20R03
