import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD18R01
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD18R03
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD18R05
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD18R07
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD18R09
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD18R11
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD18R13
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD18R15
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD18R17

/-! Every original odd mode is retained. This assembles the original source
identity from checked exact mode identities; no Gram kernel assumption occurs. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalSlaterSourceCheck18 :
    ∀ r : OddMode 18, alternateIntegerFourWords
      (integerSourceWords 18 18 r.val.val) =
        alternateIntegerFourWords (integerSlaterWords 18 r.val.val) := by
  intro r
  obtain ⟨k,hk⟩ := r.property
  have hbound : k≤8 := by
    have hr := r.val.isLt
    omega
  interval_cases k
  · have hr : r.val.val=1 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 18 1 (by decide) SlaterListCandidate.sourceListCheckD18R01
  · have hr : r.val.val=3 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 18 3 (by decide) SlaterListCandidate.sourceListCheckD18R03
  · have hr : r.val.val=5 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 18 5 (by decide) SlaterListCandidate.sourceListCheckD18R05
  · have hr : r.val.val=7 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 18 7 (by decide) SlaterListCandidate.sourceListCheckD18R07
  · have hr : r.val.val=9 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 18 9 (by decide) SlaterListCandidate.sourceListCheckD18R09
  · have hr : r.val.val=11 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 18 11 (by decide) SlaterListCandidate.sourceListCheckD18R11
  · have hr : r.val.val=13 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 18 13 (by decide) SlaterListCandidate.sourceListCheckD18R13
  · have hr : r.val.val=15 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 18 15 (by decide) SlaterListCandidate.sourceListCheckD18R15
  · have hr : r.val.val=17 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 18 17 (by decide) SlaterListCandidate.sourceListCheckD18R17

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalSlaterSourceCheck18
