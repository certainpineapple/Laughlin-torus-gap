import torus.shared.BosonNatFourOriginalPhysicalPayment
import torus.shared.BosonPhysicalMasterAssembly

/-! Discharge the last original-M4 premise in the already proved physical
master inequality. The original sector carrier and contact operator are retained. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonPhysicalThird
open TorusLean.Boson TorusLean.Boson.SpectatorControl
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonMembership
open TorusLean.Shared.PhysicalBosonLinearEquiv TorusLean.Shared.PhysicalBosonOperator
open TorusLean.Shared.PhysicalBosonFullContact TorusLean.Shared.PhysicalBosonContactForm
open TorusLean.Shared.PhysicalBosonS4Coefficients
open TorusLean.Shared.BosonPhysicalMasterAssembly
open TorusLean.Shared.BosonNatFourOriginalPhysicalPayment
open TorusLean.Shared.ThermalCoherentBosonRows
open TorusLean.Shared.BosonSystole20Scalar TorusLean.Fermion.LatticePacking

theorem physical_master_systole_twenty (G : Geometry) (theta : Twist) (M : ℕ)
    (f : PhysicalBosonCarrier G theta M) (hG : 20≤systole G) :
    actualKForm G theta ((physicalSectorEquiv G theta M).symm f).val +
      lowerA*actualParticleContactEnergy G M f.val +
      lowerB*(normalOrderedFourBodyForm G theta ((physicalSectorEquiv G theta M).symm f).val).re ≤
      (sectorInner G M f.val
        (transportedContactHamiltonian G theta M (transportedContactHamiltonian G theta M f)).val).re := by
  apply physical_master_of_originalM4_bound G theta M f hG
  have h := originalM4SourceCellForm_allM_bound G theta M
    ((physicalSectorEquiv G theta M).symm f).val
    ((physicalSectorEquiv G theta M).symm f).property hG
  simpa only [←fullCarrier_contact_energy_same_lift G theta M f] using h

theorem physical_third_systole_twenty (G : Geometry) (theta : Twist) (M : ℕ)
    (f : PhysicalBosonCarrier G theta M) (hG : 20≤systole G) :
    actualParticleContactEnergy G M f.val/3 ≤
      (sectorInner G M f.val
        (transportedContactHamiltonian G theta M (transportedContactHamiltonian G theta M f)).val).re := by
  apply physical_third_of_originalM4_bound G theta M f hG
  have h := originalM4SourceCellForm_allM_bound G theta M
    ((physicalSectorEquiv G theta M).symm f).val
    ((physicalSectorEquiv G theta M).symm f).property hG
  simpa only [←fullCarrier_contact_energy_same_lift G theta M f] using h

#print axioms physical_master_systole_twenty
#print axioms physical_third_systole_twenty
end TorusLean.Shared.BosonPhysicalThird
