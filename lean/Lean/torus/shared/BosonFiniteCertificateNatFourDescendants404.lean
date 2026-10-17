import torus.shared.BosonFiniteCertificateNatFourDescendantCOMAverageExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendants404P0
import torus.shared.BosonFiniteCertificateNatFourDescendants404P1
import torus.shared.BosonFiniteCertificateNatFourDescendants404P2
import torus.shared.BosonFiniteCertificateNatFourDescendants404P3
import torus.shared.BosonFiniteCertificateNatFourDescendants404P4
import torus.shared.BosonFiniteCertificateNatFourDescendants404P5
import torus.shared.BosonFiniteCertificateNatFourDescendants404P6
import torus.shared.BosonFiniteCertificateNatFourDescendants404P7
import torus.shared.BosonFiniteCertificateNatFourDescendants404P8
import torus.shared.BosonFiniteCertificateNatFourDescendants404P9
import torus.shared.BosonFiniteCertificateNatFourDescendants404P10
import torus.shared.BosonFiniteCertificateNatFourDescendants404P11
import torus.shared.BosonFiniteCertificateNatFourDescendants404P12

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

def f404descForms : ℕ → Matrix (Fin 2) (Fin 2) ℚ
  | 0 => f404desc0Form
  | 1 => f404desc1Form
  | 2 => f404desc2Form
  | 3 => f404desc3Form
  | 4 => f404desc4Form
  | 5 => f404desc5Form
  | 6 => f404desc6Form
  | 7 => f404desc7Form
  | 8 => f404desc8Form
  | 9 => f404desc9Form
  | 10 => f404desc10Form
  | 11 => f404desc11Form
  | 12 => f404desc12Form
  | _ => 0

theorem f404_COM_average_check :
    (∑ k ∈ Finset.range 13, natFourOriginalCOMWeight k • f404descForms k)=b404average := by
  decide +kernel

#print axioms f404_COM_average_check

theorem f404_actual_COM_matrix (x y : Fin 2 → ℂ) :
    natFourOriginalCOMForm
      (natFourWordBlock f404basis (complexify b404relative *ᵥ x))
      (natFourWordBlock f404basis (complexify b404relative *ᵥ y))=
      star x ⬝ᵥ (complexify b404average *ᵥ y) := by
  apply natFour_COM_source_matrix_form_explicit 4
    f404basis b404relative
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 4 f404basis
      f404_basis_enumeration (complexify b404relative *ᵥ x)).1)
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 4 f404basis
      f404_basis_enumeration (complexify b404relative *ᵥ x)).2)
    f404descForms _ b404average f404_COM_average_check x y
  intro k hk u v
  have hkN : k<13 := hk
  interval_cases k
  · exact f404desc0_source_form u v
  · exact f404desc1_source_form u v
  · exact f404desc2_source_form u v
  · exact f404desc3_source_form u v
  · exact f404desc4_source_form u v
  · exact f404desc5_source_form u v
  · exact f404desc6_source_form u v
  · exact f404desc7_source_form u v
  · exact f404desc8_source_form u v
  · exact f404desc9_source_form u v
  · exact f404desc10_source_form u v
  · exact f404desc11_source_form u v
  · exact f404desc12_source_form u v

#print axioms f404_actual_COM_matrix
end TorusLean.BosonFiniteCertificate
