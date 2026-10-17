import torus.shared.BosonFiniteCertificateNatFourDescendantCOMAverageExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendants403P0
import torus.shared.BosonFiniteCertificateNatFourDescendants403P1
import torus.shared.BosonFiniteCertificateNatFourDescendants403P2
import torus.shared.BosonFiniteCertificateNatFourDescendants403P3
import torus.shared.BosonFiniteCertificateNatFourDescendants403P4
import torus.shared.BosonFiniteCertificateNatFourDescendants403P5
import torus.shared.BosonFiniteCertificateNatFourDescendants403P6
import torus.shared.BosonFiniteCertificateNatFourDescendants403P7
import torus.shared.BosonFiniteCertificateNatFourDescendants403P8
import torus.shared.BosonFiniteCertificateNatFourDescendants403P9
import torus.shared.BosonFiniteCertificateNatFourDescendants403P10
import torus.shared.BosonFiniteCertificateNatFourDescendants403P11
import torus.shared.BosonFiniteCertificateNatFourDescendants403P12
import torus.shared.BosonFiniteCertificateNatFourDescendants403P13

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

def f403descForms : ℕ → Matrix (Fin 1) (Fin 1) ℚ
  | 0 => f403desc0Form
  | 1 => f403desc1Form
  | 2 => f403desc2Form
  | 3 => f403desc3Form
  | 4 => f403desc4Form
  | 5 => f403desc5Form
  | 6 => f403desc6Form
  | 7 => f403desc7Form
  | 8 => f403desc8Form
  | 9 => f403desc9Form
  | 10 => f403desc10Form
  | 11 => f403desc11Form
  | 12 => f403desc12Form
  | 13 => f403desc13Form
  | _ => 0

theorem f403_COM_average_check :
    (∑ k ∈ Finset.range 14, natFourOriginalCOMWeight k • f403descForms k)=b403average := by
  decide +kernel

#print axioms f403_COM_average_check

theorem f403_actual_COM_matrix (x y : Fin 1 → ℂ) :
    natFourOriginalCOMForm
      (natFourWordBlock f403basis (complexify b403relative *ᵥ x))
      (natFourWordBlock f403basis (complexify b403relative *ᵥ y))=
      star x ⬝ᵥ (complexify b403average *ᵥ y) := by
  apply natFour_COM_source_matrix_form_explicit 3
    f403basis b403relative
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 3 f403basis
      f403_basis_enumeration (complexify b403relative *ᵥ x)).1)
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 3 f403basis
      f403_basis_enumeration (complexify b403relative *ᵥ x)).2)
    f403descForms _ b403average f403_COM_average_check x y
  intro k hk u v
  have hkN : k<14 := hk
  interval_cases k
  · exact f403desc0_source_form u v
  · exact f403desc1_source_form u v
  · exact f403desc2_source_form u v
  · exact f403desc3_source_form u v
  · exact f403desc4_source_form u v
  · exact f403desc5_source_form u v
  · exact f403desc6_source_form u v
  · exact f403desc7_source_form u v
  · exact f403desc8_source_form u v
  · exact f403desc9_source_form u v
  · exact f403desc10_source_form u v
  · exact f403desc11_source_form u v
  · exact f403desc12_source_form u v
  · exact f403desc13_source_form u v

#print axioms f403_actual_COM_matrix
end TorusLean.BosonFiniteCertificate
