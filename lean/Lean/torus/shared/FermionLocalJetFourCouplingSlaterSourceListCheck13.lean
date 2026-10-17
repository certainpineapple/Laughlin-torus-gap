import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD13R01
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD13R03
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD13R05
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD13R07
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD13R09
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD13R11
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD13R13

/-! Every original odd mode is retained. This assembles the original source
identity from checked exact mode identities; no Gram kernel assumption occurs. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalSlaterSourceCheck13 :
    ∀ r : OddMode 13, alternateIntegerFourWords
      (integerSourceWords 13 13 r.val.val) =
        alternateIntegerFourWords (integerSlaterWords 13 r.val.val) := by
  intro r
  obtain ⟨k,hk⟩ := r.property
  have hbound : k≤6 := by
    have hr := r.val.isLt
    omega
  interval_cases k
  · have hr : r.val.val=1 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 13 1 (by decide) SlaterListCandidate.sourceListCheckD13R01
  · have hr : r.val.val=3 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 13 3 (by decide) SlaterListCandidate.sourceListCheckD13R03
  · have hr : r.val.val=5 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 13 5 (by decide) SlaterListCandidate.sourceListCheckD13R05
  · have hr : r.val.val=7 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 13 7 (by decide) SlaterListCandidate.sourceListCheckD13R07
  · have hr : r.val.val=9 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 13 9 (by decide) SlaterListCandidate.sourceListCheckD13R09
  · have hr : r.val.val=11 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 13 11 (by decide) SlaterListCandidate.sourceListCheckD13R11
  · have hr : r.val.val=13 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 13 13 (by decide) SlaterListCandidate.sourceListCheckD13R13

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalSlaterSourceCheck13
