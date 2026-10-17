import torus.shared.BosonFiniteCertificateNatFourDescendants414P0SourceForm
import torus.shared.BosonFiniteCertificateNatFourDescendants414P1SourceForm
import torus.shared.BosonFiniteCertificateNatFourDescendants414P2SourceForm
import torus.shared.BosonFiniteCertificateNatFourDescendants414Average
import torus.shared.BosonFiniteCertificateNatFourDescendantCOMAverageExplicit

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f414_actual_COM_matrix (x y : Fin 8 → ℂ) :
    natFourOriginalCOMForm
      (natFourWordBlock f414basis (complexify b414relative *ᵥ x))
      (natFourWordBlock f414basis (complexify b414relative *ᵥ y))=
      star x ⬝ᵥ (complexify b414average *ᵥ y) := by
  apply natFour_COM_source_matrix_form_explicit 14
    f414basis b414relative
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 14 f414basis
      f414_basis_enumeration (complexify b414relative *ᵥ x)).1)
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 14 f414basis
      f414_basis_enumeration (complexify b414relative *ᵥ x)).2)
    f414descForms _ b414average f414_COM_average_check x y
  intro k hk u v
  have hkN : k<3 := hk
  interval_cases k
  · exact f414desc0_source_form u v
  · exact f414desc1_source_form u v
  · exact f414desc2_source_form u v

#print axioms f414_actual_COM_matrix

end TorusLean.BosonFiniteCertificate
