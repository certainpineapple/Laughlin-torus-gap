import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD17R01
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD17R03
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD17R05
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD17R07
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD17R09
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD17R11
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD17R13
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD17R15
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD17R17

/-! Every original odd mode is retained. This assembles the original source
identity from checked exact mode identities; no Gram kernel assumption occurs. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalSlaterSourceCheck17 :
    ∀ r : OddMode 17, alternateIntegerFourWords
      (integerSourceWords 17 17 r.val.val) =
        alternateIntegerFourWords (integerSlaterWords 17 r.val.val) := by
  intro r
  obtain ⟨k,hk⟩ := r.property
  have hbound : k≤8 := by
    have hr := r.val.isLt
    omega
  interval_cases k
  · have hr : r.val.val=1 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 17 1 (by decide) SlaterListCandidate.sourceListCheckD17R01
  · have hr : r.val.val=3 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 17 3 (by decide) SlaterListCandidate.sourceListCheckD17R03
  · have hr : r.val.val=5 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 17 5 (by decide) SlaterListCandidate.sourceListCheckD17R05
  · have hr : r.val.val=7 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 17 7 (by decide) SlaterListCandidate.sourceListCheckD17R07
  · have hr : r.val.val=9 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 17 9 (by decide) SlaterListCandidate.sourceListCheckD17R09
  · have hr : r.val.val=11 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 17 11 (by decide) SlaterListCandidate.sourceListCheckD17R11
  · have hr : r.val.val=13 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 17 13 (by decide) SlaterListCandidate.sourceListCheckD17R13
  · have hr : r.val.val=15 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 17 15 (by decide) SlaterListCandidate.sourceListCheckD17R15
  · have hr : r.val.val=17 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 17 17 (by decide) SlaterListCandidate.sourceListCheckD17R17

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalSlaterSourceCheck17
