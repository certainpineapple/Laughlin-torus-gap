import torus.shared.BosonFiniteCertificateNatFourDescendants406P10LeftRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants406P10LeftRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants406P10LeftRow2

import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates406
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger416
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

private theorem f406desc10_coordinates_decode : natFourIntegerMatrix 30 f406desc10IntegerCoordinatesShared=f406desc10 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 30 f406desc10IntegerCoordinatesShared) (f406desc10) (by decide +kernel) a b

#print axioms f406desc10_coordinates_decode

theorem f406desc10_compression_check :
    f406desc10ᵀ*f416rawM4Form*f406desc10=f406desc10Form := by
  have hD := f406desc10_coordinates_decode
  have hV : f406desc10IntegerCoordinatesSharedᵀ*f416rawInteger=f406desc10IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f406desc10_integer_left_row0 b
    · exact f406desc10_integer_left_row1 b
    · exact f406desc10_integer_left_row2 b
  have hY : f406desc10IntegerLeftProductShared*f406desc10IntegerCoordinatesShared=f406desc10IntegerFormShared := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc10IntegerLeftProductShared*f406desc10IntegerCoordinatesShared) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc10IntegerFormShared) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc10IntegerLeftProductShared*f406desc10IntegerCoordinatesShared) 1 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc10IntegerFormShared) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc10IntegerLeftProductShared*f406desc10IntegerCoordinatesShared) 2 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc10IntegerFormShared) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (30*1000000000000000000000000*30) f406desc10IntegerFormShared=f406desc10Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (30*1000000000000000000000000*30) f406desc10IntegerFormShared) (f406desc10Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 30
    f416rawInteger f406desc10IntegerCoordinatesShared f406desc10IntegerLeftProductShared f406desc10IntegerFormShared
    f416rawM4Form f406desc10 f406desc10Form f416_raw_integer_check hD hV hY hF

theorem f406desc10_source_form (x y : Fin 3 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[10] (natFourWordBlock f406basis (complexify b406relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[10]
          (natFourWordBlock f406basis (complexify b406relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f406desc10Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 10
    f406basis b406relative
    f416basis f406desc10 f416rawM4Form f406desc10Form
    f406desc10_actual f416_actual_raw_M4_matrix f406desc10_compression_check x y


#print axioms f406desc10_compression_check
#print axioms f406desc10_source_form
end TorusLean.BosonFiniteCertificate
