import torus.shared.BosonFiniteCertificateNatFourDescendants406P9LeftRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants406P9LeftRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants406P9LeftRow2

import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates406
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger415
import torus.shared.BosonFiniteCertificateNatFourRaise406
import torus.shared.BosonFiniteCertificateNatFourRaise407
import torus.shared.BosonFiniteCertificateNatFourRaise408
import torus.shared.BosonFiniteCertificateNatFourRaise409
import torus.shared.BosonFiniteCertificateNatFourRaise410
import torus.shared.BosonFiniteCertificateNatFourRaise411
import torus.shared.BosonFiniteCertificateNatFourRaise412
import torus.shared.BosonFiniteCertificateNatFourRaise413
import torus.shared.BosonFiniteCertificateNatFourRaise414
import torus.shared.BosonFiniteCertificateNatFourRaise415
import torus.shared.BosonFiniteCertificate406

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

private theorem f406desc9_coordinates_decode : natFourIntegerMatrix 30 f406desc9IntegerCoordinatesShared=f406desc9 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 30 f406desc9IntegerCoordinatesShared) (f406desc9) (by decide +kernel) a b

#print axioms f406desc9_coordinates_decode

theorem f406desc9_compression_check :
    f406desc9ᵀ*f415rawM4Form*f406desc9=f406desc9Form := by
  have hD := f406desc9_coordinates_decode
  have hV : f406desc9IntegerCoordinatesSharedᵀ*f415rawInteger=f406desc9IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f406desc9_integer_left_row0 b
    · exact f406desc9_integer_left_row1 b
    · exact f406desc9_integer_left_row2 b
  have hY : f406desc9IntegerLeftProductShared*f406desc9IntegerCoordinatesShared=f406desc9IntegerFormShared := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc9IntegerLeftProductShared*f406desc9IntegerCoordinatesShared) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc9IntegerFormShared) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc9IntegerLeftProductShared*f406desc9IntegerCoordinatesShared) 1 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc9IntegerFormShared) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc9IntegerLeftProductShared*f406desc9IntegerCoordinatesShared) 2 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc9IntegerFormShared) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (30*1000000000000000000000000*30) f406desc9IntegerFormShared=f406desc9Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (30*1000000000000000000000000*30) f406desc9IntegerFormShared) (f406desc9Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 30
    f415rawInteger f406desc9IntegerCoordinatesShared f406desc9IntegerLeftProductShared f406desc9IntegerFormShared
    f415rawM4Form f406desc9 f406desc9Form f415_raw_integer_check hD hV hY hF

theorem f406desc9_source_form (x y : Fin 3 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[9] (natFourWordBlock f406basis (complexify b406relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[9]
          (natFourWordBlock f406basis (complexify b406relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f406desc9Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 9
    f406basis b406relative
    f415basis f406desc9 f415rawM4Form f406desc9Form
    f406desc9_actual f415_actual_raw_M4_matrix f406desc9_compression_check x y


#print axioms f406desc9_compression_check
#print axioms f406desc9_source_form
end TorusLean.BosonFiniteCertificate
