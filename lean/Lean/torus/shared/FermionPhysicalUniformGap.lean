import torus.shared.FermionPhysicalUniformGapTransport
import torus.shared.FermionLocalJetFourCouplingOriginalComparison

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

theorem fourExcess_nonpos (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta N) : fourExcess G theta N f≤0 := by
  exact fourExcess_nonpos_of_original_four_comparison certificateFourEnergy_le_original_target G theta N f

theorem uniform_physical_master (gamma : ℝ) (hgamma : gamma<gammaStar) :
    ∃ L : ℝ, 1≤L ∧ ∀ (G : Geometry) (theta : Twist), L≤systole G →
      ∀ (N : ℕ) (f : PhysicalFermion G theta N),
        certificateComparisonEnergy G theta (physicalCoordinates G theta N f)+
          gamma*actualFermionM1Energy G N f.val≤squareForm G theta N f := by
  exact uniform_physical_master_of_original_four_comparison certificateFourEnergy_le_original_target gamma hgamma

theorem physical_fermion_uniform_gap (gamma : ℝ)
    (hgamma : gamma<(4616733319001/100000000000000:ℝ)) :
    ∃ L : ℝ, 1≤L ∧ ∀ (G : Geometry) (theta : Twist), L≤systole G →
      ∀ (N : ℕ) (f : PhysicalFermion G theta N),
        gamma*actualFermionM1Energy G N f.val≤
          (sectorInner G N f.val
            (physicalSectorHamiltonian G theta N
              (physicalSectorHamiltonian G theta N f)).val).re := by
  exact physical_fermion_uniform_gap_of_original_four_comparison certificateFourEnergy_le_original_target gamma hgamma

theorem physical_fermion_uniform_operator_gap (gamma : ℝ)
    (hgamma : gamma<(4616733319001/100000000000000:ℝ)) :
    ∃ L : ℝ, 1≤L ∧ ∀ (G : Geometry) (theta : Twist), L≤systole G →
      ∀ (N : ℕ) (f : PhysicalFermion G theta N),
        gamma*(sectorInner G N f.val (physicalSectorHamiltonian G theta N f).val).re≤
          (sectorInner G N f.val
            (physicalSectorHamiltonian G theta N
              (physicalSectorHamiltonian G theta N f)).val).re := by
  exact physical_fermion_uniform_operator_gap_of_original_four_comparison certificateFourEnergy_le_original_target gamma hgamma

end TorusLean.Shared.FermionPhysicalUniformGap

#print axioms TorusLean.Shared.FermionPhysicalUniformGap.fourExcess_nonpos
#print axioms TorusLean.Shared.FermionPhysicalUniformGap.uniform_physical_master
#print axioms TorusLean.Shared.FermionPhysicalUniformGap.physical_fermion_uniform_gap
#print axioms TorusLean.Shared.FermionPhysicalUniformGap.physical_fermion_uniform_operator_gap
