import torus.shared.BosonFiniteCertificateNatFourDescendants410P3LeftRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants410P3LeftRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants410P3LeftRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants410P3LeftRow3
import torus.shared.BosonFiniteCertificateNatFourDescendants410P3LeftRow4

import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates410
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger413
import torus.shared.BosonFiniteCertificateNatFourRaise410
import torus.shared.BosonFiniteCertificateNatFourRaise411
import torus.shared.BosonFiniteCertificateNatFourRaise412
import torus.shared.BosonFiniteCertificateNatFourRaise413
import torus.shared.BosonFiniteCertificateNatFourRaise414
import torus.shared.BosonFiniteCertificateNatFourRaise415
import torus.shared.BosonFiniteCertificate410

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

theorem f410desc3_compression_check :
    f410desc3ᵀ*f413rawM4Form*f410desc3=f410desc3Form := by
  have hD : natFourIntegerMatrix 1260 f410desc3IntegerCoordinatesShared=f410desc3 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1260 f410desc3IntegerCoordinatesShared) (f410desc3) (by decide +kernel) a b
  have hV : f410desc3IntegerCoordinatesSharedᵀ*f413rawInteger=f410desc3IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f410desc3_integer_left_row0 b
    · exact f410desc3_integer_left_row1 b
    · exact f410desc3_integer_left_row2 b
    · exact f410desc3_integer_left_row3 b
    · exact f410desc3_integer_left_row4 b
  have hY : f410desc3IntegerLeftProductShared*f410desc3IntegerCoordinatesShared=f410desc3IntegerFormShared := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f410desc3IntegerLeftProductShared*f410desc3IntegerCoordinatesShared) 0 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f410desc3IntegerFormShared) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f410desc3IntegerLeftProductShared*f410desc3IntegerCoordinatesShared) 1 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f410desc3IntegerFormShared) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f410desc3IntegerLeftProductShared*f410desc3IntegerCoordinatesShared) 2 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f410desc3IntegerFormShared) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f410desc3IntegerLeftProductShared*f410desc3IntegerCoordinatesShared) 3 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f410desc3IntegerFormShared) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f410desc3IntegerLeftProductShared*f410desc3IntegerCoordinatesShared) 4 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f410desc3IntegerFormShared) 4 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1260*1000000000000000000000000*1260) f410desc3IntegerFormShared=f410desc3Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1260*1000000000000000000000000*1260) f410desc3IntegerFormShared) (f410desc3Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1260
    f413rawInteger f410desc3IntegerCoordinatesShared f410desc3IntegerLeftProductShared f410desc3IntegerFormShared
    f413rawM4Form f410desc3 f410desc3Form f413_raw_integer_check hD hV hY hF

theorem f410desc3_source_form (x y : Fin 5 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3] (natFourWordBlock f410basis (complexify b410relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
          (natFourWordBlock f410basis (complexify b410relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f410desc3Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 3
    f410basis b410relative
    f413basis f410desc3 f413rawM4Form f410desc3Form
    f410desc3_actual f413_actual_raw_M4_matrix f410desc3_compression_check x y


#print axioms f410desc3_compression_check
#print axioms f410desc3_source_form
end TorusLean.BosonFiniteCertificate
