import torus.shared.BosonFiniteCertificateNatFourDescendantCOMAverageExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendants409P0
import torus.shared.BosonFiniteCertificateNatFourDescendants409P1
import torus.shared.BosonFiniteCertificateNatFourDescendants409P2
import torus.shared.BosonFiniteCertificateNatFourDescendants409P3
import torus.shared.BosonFiniteCertificateNatFourDescendants409P4
import torus.shared.BosonFiniteCertificateNatFourDescendants409P5
import torus.shared.BosonFiniteCertificateNatFourDescendants409P6
import torus.shared.BosonFiniteCertificateNatFourDescendants409P7

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

def f409descForms : ℕ → Matrix (Fin 3) (Fin 3) ℚ
  | 0 => f409desc0Form
  | 1 => f409desc1Form
  | 2 => f409desc2Form
  | 3 => f409desc3Form
  | 4 => f409desc4Form
  | 5 => f409desc5Form
  | 6 => f409desc6Form
  | 7 => f409desc7Form
  | _ => 0

theorem f409_COM_average_check :
    (∑ k ∈ Finset.range 8, natFourOriginalCOMWeight k • f409descForms k)=b409average := by
  decide +kernel

#print axioms f409_COM_average_check

theorem f409_actual_COM_matrix (x y : Fin 3 → ℂ) :
    natFourOriginalCOMForm
      (natFourWordBlock f409basis (complexify b409relative *ᵥ x))
      (natFourWordBlock f409basis (complexify b409relative *ᵥ y))=
      star x ⬝ᵥ (complexify b409average *ᵥ y) := by
  apply natFour_COM_source_matrix_form_explicit 9
    f409basis b409relative
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 9 f409basis
      f409_basis_enumeration (complexify b409relative *ᵥ x)).1)
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 9 f409basis
      f409_basis_enumeration (complexify b409relative *ᵥ x)).2)
    f409descForms _ b409average f409_COM_average_check x y
  intro k hk u v
  have hkN : k<8 := hk
  interval_cases k
  · exact f409desc0_source_form u v
  · exact f409desc1_source_form u v
  · exact f409desc2_source_form u v
  · exact f409desc3_source_form u v
  · exact f409desc4_source_form u v
  · exact f409desc5_source_form u v
  · exact f409desc6_source_form u v
  · exact f409desc7_source_form u v

#print axioms f409_actual_COM_matrix
end TorusLean.BosonFiniteCertificate
