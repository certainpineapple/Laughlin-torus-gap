import torus.shared.BosonFiniteCertificateNatFourDescendants411P0SourceForm
import torus.shared.BosonFiniteCertificateNatFourDescendants411P1SourceForm
import torus.shared.BosonFiniteCertificateNatFourDescendants411P2SourceForm
import torus.shared.BosonFiniteCertificateNatFourDescendants411P3SourceForm
import torus.shared.BosonFiniteCertificateNatFourDescendants411P4SourceForm
import torus.shared.BosonFiniteCertificateNatFourDescendants411P5SourceForm
import torus.shared.BosonFiniteCertificateNatFourDescendants411Average
import torus.shared.BosonFiniteCertificateNatFourDescendantCOMAverageExplicit

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f411_actual_COM_matrix (x y : Fin 4 → ℂ) :
    natFourOriginalCOMForm
      (natFourWordBlock f411basis (complexify b411relative *ᵥ x))
      (natFourWordBlock f411basis (complexify b411relative *ᵥ y))=
      star x ⬝ᵥ (complexify b411average *ᵥ y) := by
  apply natFour_COM_source_matrix_form_explicit 11
    f411basis b411relative
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 11 f411basis
      f411_basis_enumeration (complexify b411relative *ᵥ x)).1)
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 11 f411basis
      f411_basis_enumeration (complexify b411relative *ᵥ x)).2)
    f411descForms _ b411average f411_COM_average_check x y
  intro k hk u v
  have hkN : k<6 := hk
  interval_cases k
  · exact f411desc0_source_form u v
  · exact f411desc1_source_form u v
  · exact f411desc2_source_form u v
  · exact f411desc3_source_form u v
  · exact f411desc4_source_form u v
  · exact f411desc5_source_form u v

#print axioms f411_actual_COM_matrix

end TorusLean.BosonFiniteCertificate
