import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD11R01
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD11R03
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD11R05
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD11R07
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD11R09
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD11R11

/-! Every original odd mode is retained. This assembles the original source
identity from checked exact mode identities; no Gram kernel assumption occurs. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalSlaterSourceCheck11 :
    ∀ r : OddMode 11, alternateIntegerFourWords
      (integerSourceWords 11 11 r.val.val) =
        alternateIntegerFourWords (integerSlaterWords 11 r.val.val) := by
  intro r
  obtain ⟨k,hk⟩ := r.property
  have hbound : k≤5 := by
    have hr := r.val.isLt
    omega
  interval_cases k
  · have hr : r.val.val=1 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 11 1 (by decide) SlaterListCandidate.sourceListCheckD11R01
  · have hr : r.val.val=3 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 11 3 (by decide) SlaterListCandidate.sourceListCheckD11R03
  · have hr : r.val.val=5 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 11 5 (by decide) SlaterListCandidate.sourceListCheckD11R05
  · have hr : r.val.val=7 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 11 7 (by decide) SlaterListCandidate.sourceListCheckD11R07
  · have hr : r.val.val=9 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 11 9 (by decide) SlaterListCandidate.sourceListCheckD11R09
  · have hr : r.val.val=11 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 11 11 (by decide) SlaterListCandidate.sourceListCheckD11R11

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalSlaterSourceCheck11
