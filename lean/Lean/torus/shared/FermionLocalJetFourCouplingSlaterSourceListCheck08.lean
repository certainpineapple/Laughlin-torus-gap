import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD08R01
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD08R03
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD08R05
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD08R07

/-! Every original odd mode is retained. This assembles the original source
identity from checked exact mode identities; no Gram kernel assumption occurs. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalSlaterSourceCheck08 :
    ∀ r : OddMode 8, alternateIntegerFourWords
      (integerSourceWords 8 8 r.val.val) =
        alternateIntegerFourWords (integerSlaterWords 8 r.val.val) := by
  intro r
  obtain ⟨k,hk⟩ := r.property
  have hbound : k≤3 := by
    have hr := r.val.isLt
    omega
  interval_cases k
  · have hr : r.val.val=1 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 8 1 (by decide) SlaterListCandidate.sourceListCheckD08R01
  · have hr : r.val.val=3 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 8 3 (by decide) SlaterListCandidate.sourceListCheckD08R03
  · have hr : r.val.val=5 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 8 5 (by decide) SlaterListCandidate.sourceListCheckD08R05
  · have hr : r.val.val=7 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 8 7 (by decide) SlaterListCandidate.sourceListCheckD08R07

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalSlaterSourceCheck08
