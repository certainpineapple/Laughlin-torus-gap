import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD20R01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD20R03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD20R05S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD20R07S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD20R09S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD20R11
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD20R13
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD20R15
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD20R17
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD20R19

/-! Every original odd mode is retained. This assembles the original source
identity from checked exact mode identities; no Gram kernel assumption occurs. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalSlaterSourceCheck20 :
    ∀ r : OddMode 20, alternateIntegerFourWords
      (integerSourceWords 20 20 r.val.val) =
        alternateIntegerFourWords (integerSlaterWords 20 r.val.val) := by
  intro r
  obtain ⟨k,hk⟩ := r.property
  have hbound : k≤9 := by
    have hr := r.val.isLt
    omega
  interval_cases k
  · have hr : r.val.val=1 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD20R01
  · have hr : r.val.val=3 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD20R03
  · have hr : r.val.val=5 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD20R05
  · have hr : r.val.val=7 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD20R07
  · have hr : r.val.val=9 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD20R09
  · have hr : r.val.val=11 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 20 11 (by decide) SlaterListCandidate.sourceListCheckD20R11
  · have hr : r.val.val=13 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 20 13 (by decide) SlaterListCandidate.sourceListCheckD20R13
  · have hr : r.val.val=15 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 20 15 (by decide) SlaterListCandidate.sourceListCheckD20R15
  · have hr : r.val.val=17 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 20 17 (by decide) SlaterListCandidate.sourceListCheckD20R17
  · have hr : r.val.val=19 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 20 19 (by decide) SlaterListCandidate.sourceListCheckD20R19

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalSlaterSourceCheck20
