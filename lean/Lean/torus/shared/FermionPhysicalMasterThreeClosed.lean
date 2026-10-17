import torus.shared.FermionPhysicalMasterRemainder
import torus.shared.FermionPhysicalThreeComparison

/-! Consume the actual uniform three-body comparison in the original master.
The only remaining source defect in the conclusion is the original four-body
certificate transport. No target gap or four-body payment is assumed. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionPhysicalMasterRemainder
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCarrier TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.PhysicalFermionM1Contact (actualFermionM1Energy)
open TorusLean.Shared.FermionLocalJet TorusLean.Shared.FermionLocalJet.ThreeCoupling
open TorusLean.Fermion.LatticePacking

theorem threeExcess_uniform (eps : ℝ) (heps : 0<eps) :
    ∃ L : ℝ, 1≤L ∧ ∀ (G : Geometry) (theta : Twist), L≤systole G →
      ∀ x : Space (physicalQ G theta), threeExcess G theta x≤eps*energy G theta x := by
  simpa only [threeExcess,singleForm,planeTail,energy] using
    physical_three_comparison_uniform eps heps

/-- All five actual geometric losses are now paid at one threshold, uniform
in the physical flux, twist, particle number, and state. Only original D4 remains. -/
theorem uniform_master_with_four_excess (gamma : ℝ) (hgamma : gamma<gammaStar) :
    ∃ L : ℝ, 1≤L ∧ ∀ (G : Geometry) (theta : Twist), L≤systole G →
      ∀ (N : ℕ) (f : PhysicalFermion G theta N),
        certificateComparisonEnergy G theta (physicalCoordinates G theta N f)+
          gamma*actualFermionM1Energy G N f.val≤
            squareForm G theta N f+fourExcess G theta N f := by
  let eps := (gammaStar-gamma)/5
  have heps : 0<eps := by dsimp only [eps]; positivity
  obtain ⟨L0,h01,h0⟩ := uniform_gap_margin_with_source_excesses gamma hgamma
  obtain ⟨L3,h31,h3⟩ := threeExcess_uniform eps heps
  refine ⟨max L0 L3,h01.trans (le_max_left _ _),?_⟩
  intro G theta hG N f
  have hm := h0 G theta ((le_max_left _ _).trans hG) N f
  have ht := h3 G theta ((le_max_right _ _).trans hG) (physicalCoordinates G theta N f)
  rw [energy_actual] at ht
  dsimp only [eps] at ht
  linarith

/-- This is still explicitly a four-body-remainder theorem. The true original
K4 comparison must remove fourExcess before a physical spectral gap is obtained. -/
theorem uniform_gap_with_four_excess (gamma : ℝ) (hgamma : gamma<gammaStar) :
    ∃ L : ℝ, 1≤L ∧ ∀ (G : Geometry) (theta : Twist), L≤systole G →
      ∀ (N : ℕ) (f : PhysicalFermion G theta N),
        gamma*actualFermionM1Energy G N f.val≤
          squareForm G theta N f+fourExcess G theta N f := by
  obtain ⟨L,hL1,hL⟩ := uniform_master_with_four_excess gamma hgamma
  refine ⟨L,hL1,?_⟩
  intro G theta hG N f
  have hm := hL G theta hG N f
  have hp := certificate_comparison_integral_nonneg G theta (physicalCoordinates G theta N f)
  linarith

end TorusLean.Shared.FermionPhysicalMasterRemainder
