import torus.shared.BosonFiniteCertificateNatFourDescendants410Average
import torus.shared.BosonFiniteCertificateNatFourDescendantCOMAverageExplicit

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f410_actual_COM_matrix (x y : Fin 5 → ℂ) :
    natFourOriginalCOMForm
      (natFourWordBlock f410basis (complexify b410relative *ᵥ x))
      (natFourWordBlock f410basis (complexify b410relative *ᵥ y))=
      star x ⬝ᵥ (complexify b410average *ᵥ y) := by
  apply natFour_COM_source_matrix_form_explicit 10
    f410basis b410relative
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 10 f410basis
      f410_basis_enumeration (complexify b410relative *ᵥ x)).1)
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 10 f410basis
      f410_basis_enumeration (complexify b410relative *ᵥ x)).2)
    f410descForms _ b410average f410_COM_average_check x y
  intro k hk u v
  have hkN : k<7 := hk
  interval_cases k
  · exact f410desc0_source_form u v
  · exact f410desc1_source_form u v
  · exact f410desc2_source_form u v
  · exact f410desc3_source_form u v
  · exact f410desc4_source_form u v
  · exact f410desc5_source_form u v
  · exact f410desc6_source_form u v

#print axioms f410_actual_COM_matrix

end TorusLean.BosonFiniteCertificate
