import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD05R01
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD05R03
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD05R05

/-! Every original odd mode is retained. This assembles the original source
identity from checked exact mode identities; no Gram kernel assumption occurs. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalSlaterSourceCheck05 :
    ∀ r : OddMode 5, alternateIntegerFourWords
      (integerSourceWords 5 5 r.val.val) =
        alternateIntegerFourWords (integerSlaterWords 5 r.val.val) := by
  intro r
  obtain ⟨k,hk⟩ := r.property
  have hbound : k≤2 := by
    have hr := r.val.isLt
    omega
  interval_cases k
  · have hr : r.val.val=1 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 5 1 (by decide) SlaterListCandidate.sourceListCheckD05R01
  · have hr : r.val.val=3 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 5 3 (by decide) SlaterListCandidate.sourceListCheckD05R03
  · have hr : r.val.val=5 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 5 5 (by decide) SlaterListCandidate.sourceListCheckD05R05

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalSlaterSourceCheck05
