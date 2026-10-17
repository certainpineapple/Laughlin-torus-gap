import torus.shared.BosonFiniteCertificateNatFourDescendantCOMAverageExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendants401P0
import torus.shared.BosonFiniteCertificateNatFourDescendants401P1
import torus.shared.BosonFiniteCertificateNatFourDescendants401P2
import torus.shared.BosonFiniteCertificateNatFourDescendants401P3
import torus.shared.BosonFiniteCertificateNatFourDescendants401P4
import torus.shared.BosonFiniteCertificateNatFourDescendants401P5
import torus.shared.BosonFiniteCertificateNatFourDescendants401P6
import torus.shared.BosonFiniteCertificateNatFourDescendants401P7
import torus.shared.BosonFiniteCertificateNatFourDescendants401P8
import torus.shared.BosonFiniteCertificateNatFourDescendants401P9
import torus.shared.BosonFiniteCertificateNatFourDescendants401P10
import torus.shared.BosonFiniteCertificateNatFourDescendants401P11
import torus.shared.BosonFiniteCertificateNatFourDescendants401P12
import torus.shared.BosonFiniteCertificateNatFourDescendants401P13
import torus.shared.BosonFiniteCertificateNatFourDescendants401P14
import torus.shared.BosonFiniteCertificateNatFourDescendants401P15

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

def f401descForms : ℕ → Matrix (Fin 0) (Fin 0) ℚ
  | 0 => f401desc0Form
  | 1 => f401desc1Form
  | 2 => f401desc2Form
  | 3 => f401desc3Form
  | 4 => f401desc4Form
  | 5 => f401desc5Form
  | 6 => f401desc6Form
  | 7 => f401desc7Form
  | 8 => f401desc8Form
  | 9 => f401desc9Form
  | 10 => f401desc10Form
  | 11 => f401desc11Form
  | 12 => f401desc12Form
  | 13 => f401desc13Form
  | 14 => f401desc14Form
  | 15 => f401desc15Form
  | _ => 0

theorem f401_COM_average_check :
    (∑ k ∈ Finset.range 16, natFourOriginalCOMWeight k • f401descForms k)=b401average := by
  decide +kernel

#print axioms f401_COM_average_check

theorem f401_actual_COM_matrix (x y : Fin 0 → ℂ) :
    natFourOriginalCOMForm
      (natFourWordBlock f401basis (complexify b401relative *ᵥ x))
      (natFourWordBlock f401basis (complexify b401relative *ᵥ y))=
      star x ⬝ᵥ (complexify b401average *ᵥ y) := by
  apply natFour_COM_source_matrix_form_explicit 1
    f401basis b401relative
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 1 f401basis
      f401_basis_enumeration (complexify b401relative *ᵥ x)).1)
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 1 f401basis
      f401_basis_enumeration (complexify b401relative *ᵥ x)).2)
    f401descForms _ b401average f401_COM_average_check x y
  intro k hk u v
  have hkN : k<16 := hk
  interval_cases k
  · exact f401desc0_source_form u v
  · exact f401desc1_source_form u v
  · exact f401desc2_source_form u v
  · exact f401desc3_source_form u v
  · exact f401desc4_source_form u v
  · exact f401desc5_source_form u v
  · exact f401desc6_source_form u v
  · exact f401desc7_source_form u v
  · exact f401desc8_source_form u v
  · exact f401desc9_source_form u v
  · exact f401desc10_source_form u v
  · exact f401desc11_source_form u v
  · exact f401desc12_source_form u v
  · exact f401desc13_source_form u v
  · exact f401desc14_source_form u v
  · exact f401desc15_source_form u v

#print axioms f401_actual_COM_matrix
end TorusLean.BosonFiniteCertificate
