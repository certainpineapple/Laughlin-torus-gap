import torus.shared.BosonDoubleContractionBudget
import torus.shared.ThermalCoherentBosonRowOriginalThreeIntegral
import torus.shared.ThermalCoherentBosonRowOriginalFourLift
import torus.shared.ThermalCoherentAllCoreM3Payment

/-! Conditional assembly on the original full physical boson carrier. The
Hamiltonian square, positive original row square, original full-L3/full-L4
source integrals, and metric remainder are independently defined objects.
Only the displayed upper bound for the original M4 source cell form remains
a premise. Discharging that premise requires the complete N4 certificate and
its genuine COM/cell transport; this file does not assert that discharge. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonPhysicalMasterAssembly
open MeasureTheory TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.Boson.PhysicalContactLiftCandidate
  (contactCoreHamiltonian contactPairCoordinates contactCoreHamiltonian_nonneg)
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.PhysicalBosonLinearEquiv
open TorusLean.Shared.PhysicalBosonOperator TorusLean.Shared.PhysicalBosonSquare
open TorusLean.Shared.PhysicalBosonContactForm TorusLean.Shared.PhysicalBosonFullContact
open TorusLean.Shared.PhysicalBosonS4Coefficients TorusLean.Shared.PhysicalBosonS4Positive
open TorusLean.Shared.BosonLiftSquare TorusLean.Shared.BosonPairContractions
open TorusLean.Shared.BosonDoubleContractionBudget
open TorusLean.Shared.PhysicalBosonSingleTailPayment
open TorusLean.Shared.ThermalCoherentBosonRows
open TorusLean.Shared.ThermalCoherentBosonRowOriginalThree
open TorusLean.Shared.ThermalCoherentBosonRowOriginalFourLift
open TorusLean.Shared.BosonNatThreeSourceEnergyComparison
open TorusLean.Shared.ThermalCoherentAllCorePayments
open TorusLean.Shared.ThermalCoherentAllCoreM3Payment
open TorusLean.Shared.BosonSystole20Scalar TorusLean.Fermion.LatticePacking
open scoped BigOperators
local instance master_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

/-- Both original source integrals in the actual positive row-square identity,
with the original charge-two measure and the same contact Hamiltonian. -/
theorem actualKForm_original_source_decomposition (G : Geometry) (theta : Twist)
    (p : Core (OrbitalIndex G theta) ℂ) :
    actualKForm G theta p = eta*(ip p (contactCoreHamiltonian G theta p)).re +
      originalM3SourceCellForm G theta p + originalM4SourceCellForm G theta p +
      actualMetricForm G theta p := by
  rw [actualKForm_normal_order,actualRows_three_original_integral,
    (actualRows_four_original_L4_integral G theta p).2]

/-- The real form of the unchanged physical Hamiltonian square on every
particle number, with exactly its original normal S4 and two CCR contractions. -/
theorem physical_contact_square_real (G : Geometry) (theta : Twist) (M : ℕ)
    (f : PhysicalBosonCarrier G theta M) :
    (sectorInner G M f.val
      (transportedContactHamiltonian G theta M (transportedContactHamiltonian G theta M f)).val).re =
    (normalOrderedFourBodyForm G theta ((physicalSectorEquiv G theta M).symm f).val).re +
      originalSingleForm G theta ((physicalSectorEquiv G theta M).symm f).val +
      (ip ((physicalSectorEquiv G theta M).symm f).val
        (contractionLift (contactPairCoordinates G theta) doubleContraction
          ((physicalSectorEquiv G theta M).symm f).val)).re := by
  rw [←physicalSectorLinearEquiv_toEquiv]
  simpa only [LinearEquiv.coe_symm_toEquiv,Complex.add_re,originalSingleForm,ip] using
    congrArg Complex.re (physical_contact_square_form G theta M f)

/-- All-M same-H master inequality, conditional only on the stated genuine
original full-L4 source upper bound. No new form substitutes for that source. -/
theorem physical_master_of_originalM4_bound (G : Geometry) (theta : Twist) (M : ℕ)
    (f : PhysicalBosonCarrier G theta M) (hG : 20≤systole G)
    (h4 : originalM4SourceCellForm G theta ((physicalSectorEquiv G theta M).symm f).val ≤
      alpha*sAllowance*(normalOrderedFourBodyForm G theta ((physicalSectorEquiv G theta M).symm f).val).re +
        delta*c4*sAllowance^2*
          (2*cAllowance*(normalOrderedFourBodyForm G theta ((physicalSectorEquiv G theta M).symm f).val).re +
            actualParticleContactEnergy G M f.val)) :
    actualKForm G theta ((physicalSectorEquiv G theta M).symm f).val +
      lowerA*actualParticleContactEnergy G M f.val +
      lowerB*(normalOrderedFourBodyForm G theta ((physicalSectorEquiv G theta M).symm f).val).re ≤
      (sectorInner G M f.val
        (transportedContactHamiltonian G theta M (transportedContactHamiltonian G theta M f)).val).re := by
  let p : Core (OrbitalIndex G theta) ℂ := ((physicalSectorEquiv G theta M).symm f).val
  let H : ℝ := actualParticleContactEnergy G M f.val
  let S : ℝ := (normalOrderedFourBodyForm G theta p).re
  let J : ℝ := originalSingleForm G theta p
  let D : ℝ := (ip p (contractionLift (contactPairCoordinates G theta) doubleContraction p)).re
  let K : ℝ := actualKForm G theta p
  let L3 : ℝ := originalM3SourceCellForm G theta p
  let L4 : ℝ := originalM4SourceCellForm G theta p
  let Rg : ℝ := actualMetricForm G theta p
  let Hsq : ℝ := (sectorInner G M f.val
    (transportedContactHamiltonian G theta M (transportedContactHamiltonian G theta M f)).val).re
  have he : (ip p (contactCoreHamiltonian G theta p)).re=H :=
    (fullCarrier_contact_energy_same_lift G theta M f).symm
  have hk : K=eta*H+L3+L4+Rg := by
    simpa only [he] using actualKForm_original_source_decomposition G theta p
  have hs : Hsq=S+J+D := physical_contact_square_real G theta M f
  have hd : (1-allowance)*H≤D := doubleContraction_fullCarrier_twenty G theta hG M f
  have h3 : L3≤J+sAllowance*(c9+delta*c3)*(cAllowance*S+H) := by
    simpa only [he] using originalM3SourceCellForm_allM_bound G theta M p
      ((physicalSectorEquiv G theta M).symm f).property hG
  have hRg : Rg≤(kappaAllowance*c3*sAllowance)*(cAllowance*S+H) := by
    have hb := (le_abs_self (actualMetricForm G theta p)).trans (metric_allCore G theta p hG)
    simpa only [he] using hb
  change L4≤alpha*sAllowance*S+delta*c4*sAllowance^2*(2*cAllowance*S+H) at h4
  change K+lowerA*H+lowerB*S≤Hsq
  rw [hk,hs]
  dsimp only [lowerA,lowerB,budgetA,budgetB]
  rw [show (1+allowance)=sAllowance from rfl]
  nlinarith only [h3,h4,hRg,hd]

/-- The numerical third follows for the original physical contact operator
under exactly the same remaining original-M4 source bound, for every M. -/
theorem physical_third_of_originalM4_bound (G : Geometry) (theta : Twist) (M : ℕ)
    (f : PhysicalBosonCarrier G theta M) (hG : 20≤systole G)
    (h4 : originalM4SourceCellForm G theta ((physicalSectorEquiv G theta M).symm f).val ≤
      alpha*sAllowance*(normalOrderedFourBodyForm G theta ((physicalSectorEquiv G theta M).symm f).val).re +
        delta*c4*sAllowance^2*
          (2*cAllowance*(normalOrderedFourBodyForm G theta ((physicalSectorEquiv G theta M).symm f).val).re +
            actualParticleContactEnergy G M f.val)) :
    actualParticleContactEnergy G M f.val/3 ≤
      (sectorInner G M f.val
        (transportedContactHamiltonian G theta M (transportedContactHamiltonian G theta M f)).val).re := by
  have hH : 0≤actualParticleContactEnergy G M f.val := by
    rw [fullCarrier_contact_energy_same_lift]
    exact contactCoreHamiltonian_nonneg G theta _
  exact scalar_master_implies_third _ _ _ _ lowerA lowerB hH
    (actualKForm_nonneg G theta _) (normalOrderedFourBodyForm_nonneg G theta _)
    le_rfl le_rfl (physical_master_of_originalM4_bound G theta M f hG h4)

#print axioms actualKForm_original_source_decomposition
#print axioms physical_contact_square_real
#print axioms physical_master_of_originalM4_bound
#print axioms physical_third_of_originalM4_bound
end TorusLean.Shared.BosonPhysicalMasterAssembly
