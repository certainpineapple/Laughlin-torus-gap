import torus.shared.BosonFiniteCertificateNatFourDescendantCOMAverageExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendants416SourceForm
import torus.shared.BosonFiniteCertificateNatFourDescendants416Average

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

theorem f416_actual_COM_matrix (x y : Fin 10 → ℂ) :
    natFourOriginalCOMForm
      (natFourWordBlock f416basis (complexify b416relative *ᵥ x))
      (natFourWordBlock f416basis (complexify b416relative *ᵥ y))=
      star x ⬝ᵥ (complexify b416average *ᵥ y) := by
  apply natFour_COM_source_matrix_form_explicit 16
    f416basis b416relative
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 16 f416basis
      f416_basis_enumeration (complexify b416relative *ᵥ x)).1)
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 16 f416basis
      f416_basis_enumeration (complexify b416relative *ᵥ x)).2)
    f416descForms _ b416average f416_COM_average_check x y
  intro k hk u v
  have hkN : k<1 := hk
  interval_cases k
  · exact f416desc0_source_form u v

#print axioms f416_actual_COM_matrix
end TorusLean.BosonFiniteCertificate
