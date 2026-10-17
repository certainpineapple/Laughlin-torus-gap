import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD15R01
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD15R03
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD15R05
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD15R07
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD15R09
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD15R11
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD15R13
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD15R15

/-! Every original odd mode is retained. This assembles the original source
identity from checked exact mode identities; no Gram kernel assumption occurs. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalSlaterSourceCheck15 :
    ∀ r : OddMode 15, alternateIntegerFourWords
      (integerSourceWords 15 15 r.val.val) =
        alternateIntegerFourWords (integerSlaterWords 15 r.val.val) := by
  intro r
  obtain ⟨k,hk⟩ := r.property
  have hbound : k≤7 := by
    have hr := r.val.isLt
    omega
  interval_cases k
  · have hr : r.val.val=1 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 15 1 (by decide) SlaterListCandidate.sourceListCheckD15R01
  · have hr : r.val.val=3 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 15 3 (by decide) SlaterListCandidate.sourceListCheckD15R03
  · have hr : r.val.val=5 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 15 5 (by decide) SlaterListCandidate.sourceListCheckD15R05
  · have hr : r.val.val=7 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 15 7 (by decide) SlaterListCandidate.sourceListCheckD15R07
  · have hr : r.val.val=9 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 15 9 (by decide) SlaterListCandidate.sourceListCheckD15R09
  · have hr : r.val.val=11 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 15 11 (by decide) SlaterListCandidate.sourceListCheckD15R11
  · have hr : r.val.val=13 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 15 13 (by decide) SlaterListCandidate.sourceListCheckD15R13
  · have hr : r.val.val=15 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 15 15 (by decide) SlaterListCandidate.sourceListCheckD15R15

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalSlaterSourceCheck15
