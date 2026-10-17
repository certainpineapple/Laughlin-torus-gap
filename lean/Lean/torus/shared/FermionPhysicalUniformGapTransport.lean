import torus.shared.FermionPhysicalMasterThreeClosed

/-! Dependency-parameterized verification of the exact original four final proofs.
Only the full original K4 comparison is a premise; final wrappers supply it. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.Shared.FermionPhysicalUniformGap
open MeasureTheory
open scoped BigOperators
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCarrier TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.PhysicalBosonSector (sectorInner)
open TorusLean.Shared.PhysicalFermionM1Contact TorusLean.Shared.PhysicalFermionNormalSquare
open TorusLean.Shared.FermionRelativeFrame TorusLean.Shared.FermionLocalJet
open TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.FermionPhysicalMasterRemainder
open TorusLean.Fermion.LatticePacking

theorem fourExcess_nonpos_of_original_four_comparison
    (hcomparison : ∀ (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)),
    certificateFourEnergy G theta x ≤
      (∫ R, ∑ d : Fin 23, occupationNormSq (physicalQ G theta)
        (paperFourBodyJet G theta d.val R x) ∂cellMeasure G 4) +
      (3/1000000:ℝ) * coupledFourEnergy G theta x)
    (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta N) : fourExcess G theta N f≤0 := by
  have h := hcomparison G theta
    (physicalCoordinates G theta N f)
  change certificateFourEnergy G theta (physicalCoordinates G theta N f)≤
    physicalFourJetEnergyAll G theta N 22 f+
      epsilonF*coupledFourEnergy G theta (physicalCoordinates G theta N f) at h
  unfold fourExcess
  linarith only [h]

#print axioms fourExcess_nonpos_of_original_four_comparison

theorem uniform_physical_master_of_original_four_comparison
    (hcomparison : ∀ (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)),
    certificateFourEnergy G theta x ≤
      (∫ R, ∑ d : Fin 23, occupationNormSq (physicalQ G theta)
        (paperFourBodyJet G theta d.val R x) ∂cellMeasure G 4) +
      (3/1000000:ℝ) * coupledFourEnergy G theta x)
    (gamma : ℝ) (hgamma : gamma<gammaStar) :
    ∃ L : ℝ, 1≤L ∧ ∀ (G : Geometry) (theta : Twist), L≤systole G →
      ∀ (N : ℕ) (f : PhysicalFermion G theta N),
        certificateComparisonEnergy G theta (physicalCoordinates G theta N f)+
          gamma*actualFermionM1Energy G N f.val≤squareForm G theta N f := by
  obtain ⟨L,hL1,hL⟩ := uniform_master_with_four_excess gamma hgamma
  refine ⟨L,hL1,?_⟩
  intro G theta hG N f
  have hm := hL G theta hG N f
  have hf := fourExcess_nonpos_of_original_four_comparison hcomparison G theta N f
  linarith only [hm,hf]

#print axioms uniform_physical_master_of_original_four_comparison

theorem physical_fermion_uniform_gap_of_original_four_comparison
    (hcomparison : ∀ (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)),
    certificateFourEnergy G theta x ≤
      (∫ R, ∑ d : Fin 23, occupationNormSq (physicalQ G theta)
        (paperFourBodyJet G theta d.val R x) ∂cellMeasure G 4) +
      (3/1000000:ℝ) * coupledFourEnergy G theta x)
    (gamma : ℝ)
    (hgamma : gamma<(4616733319001/100000000000000:ℝ)) :
    ∃ L : ℝ, 1≤L ∧ ∀ (G : Geometry) (theta : Twist), L≤systole G →
      ∀ (N : ℕ) (f : PhysicalFermion G theta N),
        gamma*actualFermionM1Energy G N f.val≤
          (sectorInner G N f.val
            (physicalSectorHamiltonian G theta N
              (physicalSectorHamiltonian G theta N f)).val).re := by
  have hg : gamma<gammaStar := by simpa only [gammaStar] using hgamma
  obtain ⟨L,hL1,hL⟩ := uniform_physical_master_of_original_four_comparison hcomparison gamma hg
  refine ⟨L,hL1,?_⟩
  intro G theta hG N f
  have hm := hL G theta hG N f
  have hp := certificate_comparison_integral_nonneg G theta
    (physicalCoordinates G theta N f)
  change gamma*actualFermionM1Energy G N f.val≤squareForm G theta N f
  linarith only [hm,hp]

#print axioms physical_fermion_uniform_gap_of_original_four_comparison

theorem physical_fermion_uniform_operator_gap_of_original_four_comparison
    (hcomparison : ∀ (G : Geometry) (theta : Twist)
    (x : Space (physicalQ G theta)),
    certificateFourEnergy G theta x ≤
      (∫ R, ∑ d : Fin 23, occupationNormSq (physicalQ G theta)
        (paperFourBodyJet G theta d.val R x) ∂cellMeasure G 4) +
      (3/1000000:ℝ) * coupledFourEnergy G theta x)
    (gamma : ℝ)
    (hgamma : gamma<(4616733319001/100000000000000:ℝ)) :
    ∃ L : ℝ, 1≤L ∧ ∀ (G : Geometry) (theta : Twist), L≤systole G →
      ∀ (N : ℕ) (f : PhysicalFermion G theta N),
        gamma*(sectorInner G N f.val (physicalSectorHamiltonian G theta N f).val).re≤
          (sectorInner G N f.val
            (physicalSectorHamiltonian G theta N
              (physicalSectorHamiltonian G theta N f)).val).re := by
  obtain ⟨L,hL1,hL⟩ := physical_fermion_uniform_gap_of_original_four_comparison hcomparison gamma hgamma
  refine ⟨L,hL1,?_⟩
  intro G theta hG N f
  rw [physicalSectorHamiltonian_actual_energy]
  exact hL G theta hG N f

#print axioms physical_fermion_uniform_operator_gap_of_original_four_comparison

end TorusLean.Shared.FermionPhysicalUniformGap
