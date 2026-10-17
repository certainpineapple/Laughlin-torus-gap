import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD19R01
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD19R03
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD19R05
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD19R07
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD19R09
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD19R11
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD19R13
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD19R15
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD19R17
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD19R19

/-! Every original odd mode is retained. This assembles the original source
identity from checked exact mode identities; no Gram kernel assumption occurs. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalSlaterSourceCheck19 :
    ∀ r : OddMode 19, alternateIntegerFourWords
      (integerSourceWords 19 19 r.val.val) =
        alternateIntegerFourWords (integerSlaterWords 19 r.val.val) := by
  intro r
  obtain ⟨k,hk⟩ := r.property
  have hbound : k≤9 := by
    have hr := r.val.isLt
    omega
  interval_cases k
  · have hr : r.val.val=1 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 19 1 (by decide) SlaterListCandidate.sourceListCheckD19R01
  · have hr : r.val.val=3 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 19 3 (by decide) SlaterListCandidate.sourceListCheckD19R03
  · have hr : r.val.val=5 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 19 5 (by decide) SlaterListCandidate.sourceListCheckD19R05
  · have hr : r.val.val=7 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 19 7 (by decide) SlaterListCandidate.sourceListCheckD19R07
  · have hr : r.val.val=9 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 19 9 (by decide) SlaterListCandidate.sourceListCheckD19R09
  · have hr : r.val.val=11 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 19 11 (by decide) SlaterListCandidate.sourceListCheckD19R11
  · have hr : r.val.val=13 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 19 13 (by decide) SlaterListCandidate.sourceListCheckD19R13
  · have hr : r.val.val=15 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 19 15 (by decide) SlaterListCandidate.sourceListCheckD19R15
  · have hr : r.val.val=17 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 19 17 (by decide) SlaterListCandidate.sourceListCheckD19R17
  · have hr : r.val.val=19 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 19 19 (by decide) SlaterListCandidate.sourceListCheckD19R19

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalSlaterSourceCheck19
