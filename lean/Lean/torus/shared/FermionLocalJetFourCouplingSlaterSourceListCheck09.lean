import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD09R01
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD09R03
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD09R05
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD09R07
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD09R09

/-! Every original odd mode is retained. This assembles the original source
identity from checked exact mode identities; no Gram kernel assumption occurs. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalSlaterSourceCheck09 :
    ∀ r : OddMode 9, alternateIntegerFourWords
      (integerSourceWords 9 9 r.val.val) =
        alternateIntegerFourWords (integerSlaterWords 9 r.val.val) := by
  intro r
  obtain ⟨k,hk⟩ := r.property
  have hbound : k≤4 := by
    have hr := r.val.isLt
    omega
  interval_cases k
  · have hr : r.val.val=1 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 9 1 (by decide) SlaterListCandidate.sourceListCheckD09R01
  · have hr : r.val.val=3 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 9 3 (by decide) SlaterListCandidate.sourceListCheckD09R03
  · have hr : r.val.val=5 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 9 5 (by decide) SlaterListCandidate.sourceListCheckD09R05
  · have hr : r.val.val=7 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 9 7 (by decide) SlaterListCandidate.sourceListCheckD09R07
  · have hr : r.val.val=9 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 9 9 (by decide) SlaterListCandidate.sourceListCheckD09R09

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalSlaterSourceCheck09
