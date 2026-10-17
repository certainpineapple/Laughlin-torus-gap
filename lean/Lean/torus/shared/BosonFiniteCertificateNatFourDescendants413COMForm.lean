import torus.shared.BosonFiniteCertificateNatFourDescendants413P0SourceForm
import torus.shared.BosonFiniteCertificateNatFourDescendants413P1SourceForm
import torus.shared.BosonFiniteCertificateNatFourDescendants413P2SourceForm
import torus.shared.BosonFiniteCertificateNatFourDescendants413P3SourceForm
import torus.shared.BosonFiniteCertificateNatFourDescendants413Average
import torus.shared.BosonFiniteCertificateNatFourDescendantCOMAverageExplicit

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413_actual_COM_matrix (x y : Fin 5 → ℂ) :
    natFourOriginalCOMForm
      (natFourWordBlock f413basis (complexify b413relative *ᵥ x))
      (natFourWordBlock f413basis (complexify b413relative *ᵥ y))=
      star x ⬝ᵥ (complexify b413average *ᵥ y) := by
  apply natFour_COM_source_matrix_form_explicit 13
    f413basis b413relative
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 13 f413basis
      f413_basis_enumeration (complexify b413relative *ᵥ x)).1)
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 13 f413basis
      f413_basis_enumeration (complexify b413relative *ᵥ x)).2)
    f413descForms _ b413average f413_COM_average_check x y
  intro k hk u v
  have hkN : k<4 := hk
  interval_cases k
  · exact f413desc0_source_form u v
  · exact f413desc1_source_form u v
  · exact f413desc2_source_form u v
  · exact f413desc3_source_form u v

#print axioms f413_actual_COM_matrix

end TorusLean.BosonFiniteCertificate
