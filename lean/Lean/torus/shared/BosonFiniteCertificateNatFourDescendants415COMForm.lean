import torus.shared.BosonFiniteCertificateNatFourDescendants415P0SourceForm
import torus.shared.BosonFiniteCertificateNatFourDescendants415P1SourceForm
import torus.shared.BosonFiniteCertificateNatFourDescendants415Average
import torus.shared.BosonFiniteCertificateNatFourDescendantCOMAverageExplicit

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f415_actual_COM_matrix (x y : Fin 7 → ℂ) :
    natFourOriginalCOMForm
      (natFourWordBlock f415basis (complexify b415relative *ᵥ x))
      (natFourWordBlock f415basis (complexify b415relative *ᵥ y))=
      star x ⬝ᵥ (complexify b415average *ᵥ y) := by
  apply natFour_COM_source_matrix_form_explicit 15
    f415basis b415relative
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 15 f415basis
      f415_basis_enumeration (complexify b415relative *ᵥ x)).1)
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 15 f415basis
      f415_basis_enumeration (complexify b415relative *ᵥ x)).2)
    f415descForms _ b415average f415_COM_average_check x y
  intro k hk u v
  have hkN : k<2 := hk
  interval_cases k
  · exact f415desc0_source_form u v
  · exact f415desc1_source_form u v

#print axioms f415_actual_COM_matrix

end TorusLean.BosonFiniteCertificate
