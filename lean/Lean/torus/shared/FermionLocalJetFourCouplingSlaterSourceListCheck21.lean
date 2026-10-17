import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD21R01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD21R03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD21R05S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD21R07S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD21R09S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD21R11S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD21R13
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD21R15
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD21R17
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD21R19
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD21R21

/-! Every original odd mode is retained. This assembles the original source
identity from checked exact mode identities; no Gram kernel assumption occurs. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalSlaterSourceCheck21 :
    ∀ r : OddMode 21, alternateIntegerFourWords
      (integerSourceWords 21 21 r.val.val) =
        alternateIntegerFourWords (integerSlaterWords 21 r.val.val) := by
  intro r
  obtain ⟨k,hk⟩ := r.property
  have hbound : k≤10 := by
    have hr := r.val.isLt
    omega
  interval_cases k
  · have hr : r.val.val=1 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD21R01
  · have hr : r.val.val=3 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD21R03
  · have hr : r.val.val=5 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD21R05
  · have hr : r.val.val=7 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD21R07
  · have hr : r.val.val=9 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD21R09
  · have hr : r.val.val=11 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD21R11
  · have hr : r.val.val=13 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 21 13 (by decide) SlaterListCandidate.sourceListCheckD21R13
  · have hr : r.val.val=15 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 21 15 (by decide) SlaterListCandidate.sourceListCheckD21R15
  · have hr : r.val.val=17 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 21 17 (by decide) SlaterListCandidate.sourceListCheckD21R17
  · have hr : r.val.val=19 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 21 19 (by decide) SlaterListCandidate.sourceListCheckD21R19
  · have hr : r.val.val=21 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 21 21 (by decide) SlaterListCandidate.sourceListCheckD21R21

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalSlaterSourceCheck21
