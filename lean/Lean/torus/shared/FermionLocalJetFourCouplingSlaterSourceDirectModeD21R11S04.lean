import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlockGroups
import torus.shared.FermionLocalJetFourCouplingSlaterSourceRightD21R11
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R11G00S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R11G01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R11G02S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R11G03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R11G04S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceGroupD21R11G05S04

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

private theorem fullFoldCheck :
    foldNormalBlocks [] (sourceBlocks 21 21 11)=sourceGroupEndD21R11G05S04 := by
  change foldNormalBlocks sourceGroupStartD21R11G00S04 ([sourceBlock 21 21 11 0,sourceBlock 21 21 11 1,sourceBlock 21 21 11 2,sourceBlock 21 21 11 3] ++ ([sourceBlock 21 21 11 4,sourceBlock 21 21 11 5,sourceBlock 21 21 11 6,sourceBlock 21 21 11 7] ++ ([sourceBlock 21 21 11 8,sourceBlock 21 21 11 9,sourceBlock 21 21 11 10,sourceBlock 21 21 11 11] ++ ([sourceBlock 21 21 11 12,sourceBlock 21 21 11 13,sourceBlock 21 21 11 14,sourceBlock 21 21 11 15] ++ ([sourceBlock 21 21 11 16,sourceBlock 21 21 11 17,sourceBlock 21 21 11 18,sourceBlock 21 21 11 19] ++ ([sourceBlock 21 21 11 20,sourceBlock 21 21 11 21]))))))=sourceGroupEndD21R11G05S04
  rw [foldNormalBlocks_append,sourceGroupCheckD21R11G00S04]
  have boundary00 : sourceGroupEndD21R11G00S04 =
      sourceGroupStartD21R11G01S04 := by rfl
  rw [boundary00]
  rw [foldNormalBlocks_append,sourceGroupCheckD21R11G01S04]
  have boundary01 : sourceGroupEndD21R11G01S04 =
      sourceGroupStartD21R11G02S04 := by rfl
  rw [boundary01]
  rw [foldNormalBlocks_append,sourceGroupCheckD21R11G02S04]
  have boundary02 : sourceGroupEndD21R11G02S04 =
      sourceGroupStartD21R11G03S04 := by rfl
  rw [boundary02]
  rw [foldNormalBlocks_append,sourceGroupCheckD21R11G03S04]
  have boundary03 : sourceGroupEndD21R11G03S04 =
      sourceGroupStartD21R11G04S04 := by rfl
  rw [boundary03]
  rw [foldNormalBlocks_append,sourceGroupCheckD21R11G04S04]
  have boundary04 : sourceGroupEndD21R11G04S04 =
      sourceGroupStartD21R11G05S04 := by rfl
  rw [boundary04]
  exact sourceGroupCheckD21R11G05S04

theorem sourceDirectCheckD21R11 :
    alternateIntegerFourWords (integerSourceWords 21 21 11)=
      alternateIntegerFourWords (integerSlaterWords 21 11) := by
  apply originalSlaterMode_of_blocks_check 21 11 (by decide)
  rw [fullFoldCheck,slaterWitnessCheckD21R11,slaterNormalCheckD21R11]
  rfl

end TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.SlaterListCandidate.sourceDirectCheckD21R11
