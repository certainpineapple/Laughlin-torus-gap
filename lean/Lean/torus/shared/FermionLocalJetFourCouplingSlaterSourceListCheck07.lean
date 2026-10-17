import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD07R01
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD07R03
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD07R05
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD07R07

/-! Every original odd mode is retained. This assembles the original source
identity from checked exact mode identities; no Gram kernel assumption occurs. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalSlaterSourceCheck07 :
    ∀ r : OddMode 7, alternateIntegerFourWords
      (integerSourceWords 7 7 r.val.val) =
        alternateIntegerFourWords (integerSlaterWords 7 r.val.val) := by
  intro r
  obtain ⟨k,hk⟩ := r.property
  have hbound : k≤3 := by
    have hr := r.val.isLt
    omega
  interval_cases k
  · have hr : r.val.val=1 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 7 1 (by decide) SlaterListCandidate.sourceListCheckD07R01
  · have hr : r.val.val=3 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 7 3 (by decide) SlaterListCandidate.sourceListCheckD07R03
  · have hr : r.val.val=5 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 7 5 (by decide) SlaterListCandidate.sourceListCheckD07R05
  · have hr : r.val.val=7 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 7 7 (by decide) SlaterListCandidate.sourceListCheckD07R07

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalSlaterSourceCheck07
