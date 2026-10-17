import torus.shared.BosonFiniteCertificateNatFourDescendantCOMAverageExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendants406P0
import torus.shared.BosonFiniteCertificateNatFourDescendants406P1
import torus.shared.BosonFiniteCertificateNatFourDescendants406P2
import torus.shared.BosonFiniteCertificateNatFourDescendants406P3
import torus.shared.BosonFiniteCertificateNatFourDescendants406P4
import torus.shared.BosonFiniteCertificateNatFourDescendants406P5
import torus.shared.BosonFiniteCertificateNatFourDescendants406P6
import torus.shared.BosonFiniteCertificateNatFourDescendants406P7
import torus.shared.BosonFiniteCertificateNatFourDescendants406P8
import torus.shared.BosonFiniteCertificateNatFourDescendants406P9
import torus.shared.BosonFiniteCertificateNatFourDescendants406P10

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

def f406descForms : ℕ → Matrix (Fin 3) (Fin 3) ℚ
  | 0 => f406desc0Form
  | 1 => f406desc1Form
  | 2 => f406desc2Form
  | 3 => f406desc3Form
  | 4 => f406desc4Form
  | 5 => f406desc5Form
  | 6 => f406desc6Form
  | 7 => f406desc7Form
  | 8 => f406desc8Form
  | 9 => f406desc9Form
  | 10 => f406desc10Form
  | _ => 0

theorem f406_COM_average_check :
    (∑ k ∈ Finset.range 11, natFourOriginalCOMWeight k • f406descForms k)=b406average := by
  decide +kernel

#print axioms f406_COM_average_check

theorem f406_actual_COM_matrix (x y : Fin 3 → ℂ) :
    natFourOriginalCOMForm
      (natFourWordBlock f406basis (complexify b406relative *ᵥ x))
      (natFourWordBlock f406basis (complexify b406relative *ᵥ y))=
      star x ⬝ᵥ (complexify b406average *ᵥ y) := by
  apply natFour_COM_source_matrix_form_explicit 6
    f406basis b406relative
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 6 f406basis
      f406_basis_enumeration (complexify b406relative *ᵥ x)).1)
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 6 f406basis
      f406_basis_enumeration (complexify b406relative *ᵥ x)).2)
    f406descForms _ b406average f406_COM_average_check x y
  intro k hk u v
  have hkN : k<11 := hk
  interval_cases k
  · exact f406desc0_source_form u v
  · exact f406desc1_source_form u v
  · exact f406desc2_source_form u v
  · exact f406desc3_source_form u v
  · exact f406desc4_source_form u v
  · exact f406desc5_source_form u v
  · exact f406desc6_source_form u v
  · exact f406desc7_source_form u v
  · exact f406desc8_source_form u v
  · exact f406desc9_source_form u v
  · exact f406desc10_source_form u v

#print axioms f406_actual_COM_matrix
end TorusLean.BosonFiniteCertificate
