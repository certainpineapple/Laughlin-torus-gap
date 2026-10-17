import torus.shared.BosonFiniteCertificateNatFourDescendants412P0SourceForm
import torus.shared.BosonFiniteCertificateNatFourDescendants412P1SourceForm
import torus.shared.BosonFiniteCertificateNatFourDescendants412P2SourceForm
import torus.shared.BosonFiniteCertificateNatFourDescendants412P3SourceForm
import torus.shared.BosonFiniteCertificateNatFourDescendants412P4SourceForm
import torus.shared.BosonFiniteCertificateNatFourDescendants412Average
import torus.shared.BosonFiniteCertificateNatFourDescendantCOMAverageExplicit

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f412_actual_COM_matrix (x y : Fin 7 → ℂ) :
    natFourOriginalCOMForm
      (natFourWordBlock f412basis (complexify b412relative *ᵥ x))
      (natFourWordBlock f412basis (complexify b412relative *ᵥ y))=
      star x ⬝ᵥ (complexify b412average *ᵥ y) := by
  apply natFour_COM_source_matrix_form_explicit 12
    f412basis b412relative
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 12 f412basis
      f412_basis_enumeration (complexify b412relative *ᵥ x)).1)
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 12 f412basis
      f412_basis_enumeration (complexify b412relative *ᵥ x)).2)
    f412descForms _ b412average f412_COM_average_check x y
  intro k hk u v
  have hkN : k<5 := hk
  interval_cases k
  · exact f412desc0_source_form u v
  · exact f412desc1_source_form u v
  · exact f412desc2_source_form u v
  · exact f412desc3_source_form u v
  · exact f412desc4_source_form u v

#print axioms f412_actual_COM_matrix

end TorusLean.BosonFiniteCertificate
