import torus.shared.BosonFiniteCertificateNatFourDescendantCOMAverageExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendants402P0
import torus.shared.BosonFiniteCertificateNatFourDescendants402P1
import torus.shared.BosonFiniteCertificateNatFourDescendants402P2
import torus.shared.BosonFiniteCertificateNatFourDescendants402P3
import torus.shared.BosonFiniteCertificateNatFourDescendants402P4
import torus.shared.BosonFiniteCertificateNatFourDescendants402P5
import torus.shared.BosonFiniteCertificateNatFourDescendants402P6
import torus.shared.BosonFiniteCertificateNatFourDescendants402P7
import torus.shared.BosonFiniteCertificateNatFourDescendants402P8
import torus.shared.BosonFiniteCertificateNatFourDescendants402P9
import torus.shared.BosonFiniteCertificateNatFourDescendants402P10
import torus.shared.BosonFiniteCertificateNatFourDescendants402P11
import torus.shared.BosonFiniteCertificateNatFourDescendants402P12
import torus.shared.BosonFiniteCertificateNatFourDescendants402P13
import torus.shared.BosonFiniteCertificateNatFourDescendants402P14

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

def f402descForms : ℕ → Matrix (Fin 1) (Fin 1) ℚ
  | 0 => f402desc0Form
  | 1 => f402desc1Form
  | 2 => f402desc2Form
  | 3 => f402desc3Form
  | 4 => f402desc4Form
  | 5 => f402desc5Form
  | 6 => f402desc6Form
  | 7 => f402desc7Form
  | 8 => f402desc8Form
  | 9 => f402desc9Form
  | 10 => f402desc10Form
  | 11 => f402desc11Form
  | 12 => f402desc12Form
  | 13 => f402desc13Form
  | 14 => f402desc14Form
  | _ => 0

theorem f402_COM_average_check :
    (∑ k ∈ Finset.range 15, natFourOriginalCOMWeight k • f402descForms k)=b402average := by
  decide +kernel

#print axioms f402_COM_average_check

theorem f402_actual_COM_matrix (x y : Fin 1 → ℂ) :
    natFourOriginalCOMForm
      (natFourWordBlock f402basis (complexify b402relative *ᵥ x))
      (natFourWordBlock f402basis (complexify b402relative *ᵥ y))=
      star x ⬝ᵥ (complexify b402average *ᵥ y) := by
  apply natFour_COM_source_matrix_form_explicit 2
    f402basis b402relative
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 2 f402basis
      f402_basis_enumeration (complexify b402relative *ᵥ x)).1)
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 2 f402basis
      f402_basis_enumeration (complexify b402relative *ᵥ x)).2)
    f402descForms _ b402average f402_COM_average_check x y
  intro k hk u v
  have hkN : k<15 := hk
  interval_cases k
  · exact f402desc0_source_form u v
  · exact f402desc1_source_form u v
  · exact f402desc2_source_form u v
  · exact f402desc3_source_form u v
  · exact f402desc4_source_form u v
  · exact f402desc5_source_form u v
  · exact f402desc6_source_form u v
  · exact f402desc7_source_form u v
  · exact f402desc8_source_form u v
  · exact f402desc9_source_form u v
  · exact f402desc10_source_form u v
  · exact f402desc11_source_form u v
  · exact f402desc12_source_form u v
  · exact f402desc13_source_form u v
  · exact f402desc14_source_form u v

#print axioms f402_actual_COM_matrix
end TorusLean.BosonFiniteCertificate
