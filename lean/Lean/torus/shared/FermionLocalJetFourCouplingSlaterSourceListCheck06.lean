import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD06R01
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD06R03
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD06R05

/-! Every original odd mode is retained. This assembles the original source
identity from checked exact mode identities; no Gram kernel assumption occurs. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalSlaterSourceCheck06 :
    ∀ r : OddMode 6, alternateIntegerFourWords
      (integerSourceWords 6 6 r.val.val) =
        alternateIntegerFourWords (integerSlaterWords 6 r.val.val) := by
  intro r
  obtain ⟨k,hk⟩ := r.property
  have hbound : k≤2 := by
    have hr := r.val.isLt
    omega
  interval_cases k
  · have hr : r.val.val=1 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 6 1 (by decide) SlaterListCandidate.sourceListCheckD06R01
  · have hr : r.val.val=3 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 6 3 (by decide) SlaterListCandidate.sourceListCheckD06R03
  · have hr : r.val.val=5 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 6 5 (by decide) SlaterListCandidate.sourceListCheckD06R05

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalSlaterSourceCheck06
