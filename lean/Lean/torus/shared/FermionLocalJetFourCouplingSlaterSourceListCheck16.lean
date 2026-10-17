import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD16R01
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD16R03
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD16R05
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD16R07
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD16R09
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD16R11
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD16R13
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD16R15

/-! Every original odd mode is retained. This assembles the original source
identity from checked exact mode identities; no Gram kernel assumption occurs. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalSlaterSourceCheck16 :
    ∀ r : OddMode 16, alternateIntegerFourWords
      (integerSourceWords 16 16 r.val.val) =
        alternateIntegerFourWords (integerSlaterWords 16 r.val.val) := by
  intro r
  obtain ⟨k,hk⟩ := r.property
  have hbound : k≤7 := by
    have hr := r.val.isLt
    omega
  interval_cases k
  · have hr : r.val.val=1 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 16 1 (by decide) SlaterListCandidate.sourceListCheckD16R01
  · have hr : r.val.val=3 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 16 3 (by decide) SlaterListCandidate.sourceListCheckD16R03
  · have hr : r.val.val=5 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 16 5 (by decide) SlaterListCandidate.sourceListCheckD16R05
  · have hr : r.val.val=7 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 16 7 (by decide) SlaterListCandidate.sourceListCheckD16R07
  · have hr : r.val.val=9 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 16 9 (by decide) SlaterListCandidate.sourceListCheckD16R09
  · have hr : r.val.val=11 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 16 11 (by decide) SlaterListCandidate.sourceListCheckD16R11
  · have hr : r.val.val=13 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 16 13 (by decide) SlaterListCandidate.sourceListCheckD16R13
  · have hr : r.val.val=15 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 16 15 (by decide) SlaterListCandidate.sourceListCheckD16R15

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalSlaterSourceCheck16
