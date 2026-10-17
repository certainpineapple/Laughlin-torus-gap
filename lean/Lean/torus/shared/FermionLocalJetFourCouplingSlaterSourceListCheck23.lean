import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD23R01S02
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD23R03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD23R05S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD23R07S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD23R09S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD23R11S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD23R13S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD23R15S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD23R17
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD23R19
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD23R21
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD23R23

/-! Every original odd mode is retained. This assembles the original source
identity from checked exact mode identities; no Gram kernel assumption occurs. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalSlaterSourceCheck23 :
    ∀ r : OddMode 23, alternateIntegerFourWords
      (integerSourceWords 23 23 r.val.val) =
        alternateIntegerFourWords (integerSlaterWords 23 r.val.val) := by
  intro r
  obtain ⟨k,hk⟩ := r.property
  have hbound : k≤11 := by
    have hr := r.val.isLt
    omega
  interval_cases k
  · have hr : r.val.val=1 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD23R01
  · have hr : r.val.val=3 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD23R03
  · have hr : r.val.val=5 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD23R05
  · have hr : r.val.val=7 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD23R07
  · have hr : r.val.val=9 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD23R09
  · have hr : r.val.val=11 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD23R11
  · have hr : r.val.val=13 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD23R13
  · have hr : r.val.val=15 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD23R15
  · have hr : r.val.val=17 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 23 17 (by decide) SlaterListCandidate.sourceListCheckD23R17
  · have hr : r.val.val=19 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 23 19 (by decide) SlaterListCandidate.sourceListCheckD23R19
  · have hr : r.val.val=21 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 23 21 (by decide) SlaterListCandidate.sourceListCheckD23R21
  · have hr : r.val.val=23 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 23 23 (by decide) SlaterListCandidate.sourceListCheckD23R23

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalSlaterSourceCheck23
