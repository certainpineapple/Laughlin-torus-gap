import torus.shared.BosonFiniteCertificateNatFourDescendantCOMAverageExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendants400P0
import torus.shared.BosonFiniteCertificateNatFourDescendants400P1
import torus.shared.BosonFiniteCertificateNatFourDescendants400P2
import torus.shared.BosonFiniteCertificateNatFourDescendants400P3
import torus.shared.BosonFiniteCertificateNatFourDescendants400P4
import torus.shared.BosonFiniteCertificateNatFourDescendants400P5
import torus.shared.BosonFiniteCertificateNatFourDescendants400P6
import torus.shared.BosonFiniteCertificateNatFourDescendants400P7
import torus.shared.BosonFiniteCertificateNatFourDescendants400P8
import torus.shared.BosonFiniteCertificateNatFourDescendants400P9
import torus.shared.BosonFiniteCertificateNatFourDescendants400P10
import torus.shared.BosonFiniteCertificateNatFourDescendants400P11
import torus.shared.BosonFiniteCertificateNatFourDescendants400P12
import torus.shared.BosonFiniteCertificateNatFourDescendants400P13
import torus.shared.BosonFiniteCertificateNatFourDescendants400P14
import torus.shared.BosonFiniteCertificateNatFourDescendants400P15
import torus.shared.BosonFiniteCertificateNatFourDescendants400P16

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

def f400descForms : ℕ → Matrix (Fin 1) (Fin 1) ℚ
  | 0 => f400desc0Form
  | 1 => f400desc1Form
  | 2 => f400desc2Form
  | 3 => f400desc3Form
  | 4 => f400desc4Form
  | 5 => f400desc5Form
  | 6 => f400desc6Form
  | 7 => f400desc7Form
  | 8 => f400desc8Form
  | 9 => f400desc9Form
  | 10 => f400desc10Form
  | 11 => f400desc11Form
  | 12 => f400desc12Form
  | 13 => f400desc13Form
  | 14 => f400desc14Form
  | 15 => f400desc15Form
  | 16 => f400desc16Form
  | _ => 0

theorem f400_COM_average_check :
    (∑ k ∈ Finset.range 17, natFourOriginalCOMWeight k • f400descForms k)=b400average := by
  decide +kernel

#print axioms f400_COM_average_check

theorem f400_actual_COM_matrix (x y : Fin 1 → ℂ) :
    natFourOriginalCOMForm
      (natFourWordBlock f400basis (complexify b400relative *ᵥ x))
      (natFourWordBlock f400basis (complexify b400relative *ᵥ y))=
      star x ⬝ᵥ (complexify b400average *ᵥ y) := by
  apply natFour_COM_source_matrix_form_explicit 0
    f400basis b400relative
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 0 f400basis
      f400_basis_enumeration (complexify b400relative *ᵥ x)).1)
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 0 f400basis
      f400_basis_enumeration (complexify b400relative *ᵥ x)).2)
    f400descForms _ b400average f400_COM_average_check x y
  intro k hk u v
  have hkN : k<17 := hk
  interval_cases k
  · exact f400desc0_source_form u v
  · exact f400desc1_source_form u v
  · exact f400desc2_source_form u v
  · exact f400desc3_source_form u v
  · exact f400desc4_source_form u v
  · exact f400desc5_source_form u v
  · exact f400desc6_source_form u v
  · exact f400desc7_source_form u v
  · exact f400desc8_source_form u v
  · exact f400desc9_source_form u v
  · exact f400desc10_source_form u v
  · exact f400desc11_source_form u v
  · exact f400desc12_source_form u v
  · exact f400desc13_source_form u v
  · exact f400desc14_source_form u v
  · exact f400desc15_source_form u v
  · exact f400desc16_source_form u v

#print axioms f400_actual_COM_matrix
end TorusLean.BosonFiniteCertificate
