import torus.shared.FermionLocalJetFourCouplingSlaterSourceBlocks
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD22R01S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD22R03S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD22R05S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD22R07S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD22R09S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD22R11S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceDirectModeD22R13S04
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD22R15
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD22R17
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD22R19
import torus.shared.FermionLocalJetFourCouplingSlaterSourceModeD22R21

/-! Every original odd mode is retained. This assembles the original source
identity from checked exact mode identities; no Gram kernel assumption occurs. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace TorusLean.Shared.FermionLocalJet.FourCoupling

theorem originalSlaterSourceCheck22 :
    ∀ r : OddMode 22, alternateIntegerFourWords
      (integerSourceWords 22 22 r.val.val) =
        alternateIntegerFourWords (integerSlaterWords 22 r.val.val) := by
  intro r
  obtain ⟨k,hk⟩ := r.property
  have hbound : k≤10 := by
    have hr := r.val.isLt
    omega
  interval_cases k
  · have hr : r.val.val=1 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD22R01
  · have hr : r.val.val=3 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD22R03
  · have hr : r.val.val=5 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD22R05
  · have hr : r.val.val=7 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD22R07
  · have hr : r.val.val=9 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD22R09
  · have hr : r.val.val=11 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD22R11
  · have hr : r.val.val=13 := by omega
    simpa only [hr] using SlaterListCandidate.sourceDirectCheckD22R13
  · have hr : r.val.val=15 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 22 15 (by decide) SlaterListCandidate.sourceListCheckD22R15
  · have hr : r.val.val=17 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 22 17 (by decide) SlaterListCandidate.sourceListCheckD22R17
  · have hr : r.val.val=19 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 22 19 (by decide) SlaterListCandidate.sourceListCheckD22R19
  · have hr : r.val.val=21 := by omega
    simpa only [hr] using SlaterListCandidate.originalSlaterMode_of_fast_list_check 22 21 (by decide) SlaterListCandidate.sourceListCheckD22R21

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.originalSlaterSourceCheck22
