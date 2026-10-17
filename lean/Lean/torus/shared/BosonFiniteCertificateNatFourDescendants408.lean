import torus.shared.BosonFiniteCertificateNatFourDescendantCOMAverageExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendants408P0
import torus.shared.BosonFiniteCertificateNatFourDescendants408P1
import torus.shared.BosonFiniteCertificateNatFourDescendants408P2
import torus.shared.BosonFiniteCertificateNatFourDescendants408P3
import torus.shared.BosonFiniteCertificateNatFourDescendants408P4
import torus.shared.BosonFiniteCertificateNatFourDescendants408P5
import torus.shared.BosonFiniteCertificateNatFourDescendants408P6
import torus.shared.BosonFiniteCertificateNatFourDescendants408P7
import torus.shared.BosonFiniteCertificateNatFourDescendants408P8

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

def f408descForms : ℕ → Matrix (Fin 4) (Fin 4) ℚ
  | 0 => f408desc0Form
  | 1 => f408desc1Form
  | 2 => f408desc2Form
  | 3 => f408desc3Form
  | 4 => f408desc4Form
  | 5 => f408desc5Form
  | 6 => f408desc6Form
  | 7 => f408desc7Form
  | 8 => f408desc8Form
  | _ => 0

theorem f408_COM_average_check :
    (∑ k ∈ Finset.range 9, natFourOriginalCOMWeight k • f408descForms k)=b408average := by
  decide +kernel

#print axioms f408_COM_average_check

theorem f408_actual_COM_matrix (x y : Fin 4 → ℂ) :
    natFourOriginalCOMForm
      (natFourWordBlock f408basis (complexify b408relative *ᵥ x))
      (natFourWordBlock f408basis (complexify b408relative *ᵥ y))=
      star x ⬝ᵥ (complexify b408average *ᵥ y) := by
  apply natFour_COM_source_matrix_form_explicit 8
    f408basis b408relative
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 8 f408basis
      f408_basis_enumeration (complexify b408relative *ᵥ x)).1)
    (fun x => (natFourWordBlock_bihomogeneous_of_enumeration 8 f408basis
      f408_basis_enumeration (complexify b408relative *ᵥ x)).2)
    f408descForms _ b408average f408_COM_average_check x y
  intro k hk u v
  have hkN : k<9 := hk
  interval_cases k
  · exact f408desc0_source_form u v
  · exact f408desc1_source_form u v
  · exact f408desc2_source_form u v
  · exact f408desc3_source_form u v
  · exact f408desc4_source_form u v
  · exact f408desc5_source_form u v
  · exact f408desc6_source_form u v
  · exact f408desc7_source_form u v
  · exact f408desc8_source_form u v

#print axioms f408_actual_COM_matrix
end TorusLean.BosonFiniteCertificate
