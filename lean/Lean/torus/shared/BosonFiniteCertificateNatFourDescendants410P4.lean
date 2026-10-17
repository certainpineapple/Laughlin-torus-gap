import torus.shared.BosonFiniteCertificateNatFourDescendants410P4LeftRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants410P4LeftRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants410P4LeftRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants410P4LeftRow3
import torus.shared.BosonFiniteCertificateNatFourDescendants410P4LeftRow4

import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates410
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger414
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

private theorem f410desc4_coordinates_decode : natFourIntegerMatrix 1260 f410desc4IntegerCoordinatesShared=f410desc4 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1260 f410desc4IntegerCoordinatesShared) (f410desc4) (by decide +kernel) a b

#print axioms f410desc4_coordinates_decode

theorem f410desc4_compression_check :
    f410desc4ᵀ*f414rawM4Form*f410desc4=f410desc4Form := by
  have hD := f410desc4_coordinates_decode
  have hV : f410desc4IntegerCoordinatesSharedᵀ*f414rawInteger=f410desc4IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f410desc4_integer_left_row0 b
    · exact f410desc4_integer_left_row1 b
    · exact f410desc4_integer_left_row2 b
    · exact f410desc4_integer_left_row3 b
    · exact f410desc4_integer_left_row4 b
  have hY : f410desc4IntegerLeftProductShared*f410desc4IntegerCoordinatesShared=f410desc4IntegerFormShared := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f410desc4IntegerLeftProductShared*f410desc4IntegerCoordinatesShared) 0 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f410desc4IntegerFormShared) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f410desc4IntegerLeftProductShared*f410desc4IntegerCoordinatesShared) 1 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f410desc4IntegerFormShared) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f410desc4IntegerLeftProductShared*f410desc4IntegerCoordinatesShared) 2 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f410desc4IntegerFormShared) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f410desc4IntegerLeftProductShared*f410desc4IntegerCoordinatesShared) 3 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f410desc4IntegerFormShared) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f410desc4IntegerLeftProductShared*f410desc4IntegerCoordinatesShared) 4 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f410desc4IntegerFormShared) 4 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1260*1000000000000000000000000*1260) f410desc4IntegerFormShared=f410desc4Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1260*1000000000000000000000000*1260) f410desc4IntegerFormShared) (f410desc4Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1260
    f414rawInteger f410desc4IntegerCoordinatesShared f410desc4IntegerLeftProductShared f410desc4IntegerFormShared
    f414rawM4Form f410desc4 f410desc4Form f414_raw_integer_check hD hV hY hF

theorem f410desc4_source_form (x y : Fin 5 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4] (natFourWordBlock f410basis (complexify b410relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
          (natFourWordBlock f410basis (complexify b410relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f410desc4Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 4
    f410basis b410relative
    f414basis f410desc4 f414rawM4Form f410desc4Form
    f410desc4_actual f414_actual_raw_M4_matrix f410desc4_compression_check x y


#print axioms f410desc4_compression_check
#print axioms f410desc4_source_form
end TorusLean.BosonFiniteCertificate
