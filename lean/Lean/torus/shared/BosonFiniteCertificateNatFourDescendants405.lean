import torus.shared.BosonFiniteCertificateNatFourDescendantCOMAverageExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendants405P0
import torus.shared.BosonFiniteCertificateNatFourDescendants405P1
import torus.shared.BosonFiniteCertificateNatFourDescendants405P2
import torus.shared.BosonFiniteCertificateNatFourDescendants405P3
import torus.shared.BosonFiniteCertificateNatFourDescendants405P4
import torus.shared.BosonFiniteCertificateNatFourDescendants405P5
import torus.shared.BosonFiniteCertificateNatFourDescendants405P6
import torus.shared.BosonFiniteCertificateNatFourDescendants405P7
import torus.shared.BosonFiniteCertificateNatFourDescendants405P8
import torus.shared.BosonFiniteCertificateNatFourDescendants405P9
import torus.shared.BosonFiniteCertificateNatFourDescendants405P10
import torus.shared.BosonFiniteCertificateNatFourDescendants405P11

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

def f405descForms : ℕ → Matrix (Fin 1) (Fin 1) ℚ
  | 0 => f405desc0Form
  | 1 => f405desc1Form
  | 2 => f405desc2Form
  | 3 => f405desc3Form
  | 4 => f405desc4Form
  | 5 => f405desc5Form
  | 6 => f405desc6Form
  | 7 => f405desc7Form
  | 8 => f405desc8Form
  | 9 => f405desc9Form
  | 10 => f405desc10Form
  | 11 => f405desc11Form
  | _ => 0

theorem f405_COM_average_check :
    (∑ k ∈ Finset.range 12, natFourOriginalCOMWeight k • f405descForms k)=b405average := by
  decide +kernel

#print axioms f405_COM_average_check

theorem f405_actual_COM_matrix (x y : Fin 1 → ℂ) :
    natFourOriginalCOMForm
      (natFourWordBlock f405basis (complexify b405relative *ᵥ x))
      (natFourWordBlock f405basis (complexify b405relative *ᵥ y))=
      star x ⬝ᵥ (complexify b405average *ᵥ y) := by
  apply natFour_COM_source_matrix_form_explicit 5
    f405basis b405relative
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 5 f405basis
      f405_basis_enumeration (complexify b405relative *ᵥ x)).1)
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 5 f405basis
      f405_basis_enumeration (complexify b405relative *ᵥ x)).2)
    f405descForms _ b405average f405_COM_average_check x y
  intro k hk u v
  have hkN : k<12 := hk
  interval_cases k
  · exact f405desc0_source_form u v
  · exact f405desc1_source_form u v
  · exact f405desc2_source_form u v
  · exact f405desc3_source_form u v
  · exact f405desc4_source_form u v
  · exact f405desc5_source_form u v
  · exact f405desc6_source_form u v
  · exact f405desc7_source_form u v
  · exact f405desc8_source_form u v
  · exact f405desc9_source_form u v
  · exact f405desc10_source_form u v
  · exact f405desc11_source_form u v

#print axioms f405_actual_COM_matrix
end TorusLean.BosonFiniteCertificate
