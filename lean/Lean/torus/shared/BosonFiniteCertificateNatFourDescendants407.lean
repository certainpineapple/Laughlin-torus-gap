import torus.shared.BosonFiniteCertificateNatFourDescendantCOMAverageExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendants407P0
import torus.shared.BosonFiniteCertificateNatFourDescendants407P1
import torus.shared.BosonFiniteCertificateNatFourDescendants407P2
import torus.shared.BosonFiniteCertificateNatFourDescendants407P3
import torus.shared.BosonFiniteCertificateNatFourDescendants407P4
import torus.shared.BosonFiniteCertificateNatFourDescendants407P5
import torus.shared.BosonFiniteCertificateNatFourDescendants407P6
import torus.shared.BosonFiniteCertificateNatFourDescendants407P7
import torus.shared.BosonFiniteCertificateNatFourDescendants407P8
import torus.shared.BosonFiniteCertificateNatFourDescendants407P9

/-! Genuine Nat COM descendants of the original relative basis, with every
step checked against independently verified raising actions and every form
checked against independently reconstructed raw source M4 matrices. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

def f407descForms : ℕ → Matrix (Fin 2) (Fin 2) ℚ
  | 0 => f407desc0Form
  | 1 => f407desc1Form
  | 2 => f407desc2Form
  | 3 => f407desc3Form
  | 4 => f407desc4Form
  | 5 => f407desc5Form
  | 6 => f407desc6Form
  | 7 => f407desc7Form
  | 8 => f407desc8Form
  | 9 => f407desc9Form
  | _ => 0

theorem f407_COM_average_check :
    (∑ k ∈ Finset.range 10, natFourOriginalCOMWeight k • f407descForms k)=b407average := by
  decide +kernel

#print axioms f407_COM_average_check

theorem f407_actual_COM_matrix (x y : Fin 2 → ℂ) :
    natFourOriginalCOMForm
      (natFourWordBlock f407basis (complexify b407relative *ᵥ x))
      (natFourWordBlock f407basis (complexify b407relative *ᵥ y))=
      star x ⬝ᵥ (complexify b407average *ᵥ y) := by
  apply natFour_COM_source_matrix_form_explicit 7
    f407basis b407relative
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 7 f407basis
      f407_basis_enumeration (complexify b407relative *ᵥ x)).1)
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 7 f407basis
      f407_basis_enumeration (complexify b407relative *ᵥ x)).2)
    f407descForms _ b407average f407_COM_average_check x y
  intro k hk u v
  have hkN : k<10 := hk
  interval_cases k
  · exact f407desc0_source_form u v
  · exact f407desc1_source_form u v
  · exact f407desc2_source_form u v
  · exact f407desc3_source_form u v
  · exact f407desc4_source_form u v
  · exact f407desc5_source_form u v
  · exact f407desc6_source_form u v
  · exact f407desc7_source_form u v
  · exact f407desc8_source_form u v
  · exact f407desc9_source_form u v

#print axioms f407_actual_COM_matrix
end TorusLean.BosonFiniteCertificate
