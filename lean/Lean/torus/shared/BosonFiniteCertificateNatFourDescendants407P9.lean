import torus.shared.BosonFiniteCertificateNatFourDescendants407P9LeftRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants407P9LeftRow1

import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates407
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger416
import torus.shared.BosonFiniteCertificateNatFourRaise407
import torus.shared.BosonFiniteCertificateNatFourRaise408
import torus.shared.BosonFiniteCertificateNatFourRaise409
import torus.shared.BosonFiniteCertificateNatFourRaise410
import torus.shared.BosonFiniteCertificateNatFourRaise411
import torus.shared.BosonFiniteCertificateNatFourRaise412
import torus.shared.BosonFiniteCertificateNatFourRaise413
import torus.shared.BosonFiniteCertificateNatFourRaise414
import torus.shared.BosonFiniteCertificateNatFourRaise415
import torus.shared.BosonFiniteCertificate407

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

private theorem f407desc9_coordinates_decode : natFourIntegerMatrix 60 f407desc9IntegerCoordinatesShared=f407desc9 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 60 f407desc9IntegerCoordinatesShared) (f407desc9) (by decide +kernel) a b

#print axioms f407desc9_coordinates_decode

theorem f407desc9_compression_check :
    f407desc9ᵀ*f416rawM4Form*f407desc9=f407desc9Form := by
  have hD := f407desc9_coordinates_decode
  have hV : f407desc9IntegerCoordinatesSharedᵀ*f416rawInteger=f407desc9IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f407desc9_integer_left_row0 b
    · exact f407desc9_integer_left_row1 b
  have hY : f407desc9IntegerLeftProductShared*f407desc9IntegerCoordinatesShared=f407desc9IntegerFormShared := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc9IntegerLeftProductShared*f407desc9IntegerCoordinatesShared) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc9IntegerFormShared) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc9IntegerLeftProductShared*f407desc9IntegerCoordinatesShared) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc9IntegerFormShared) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (60*1000000000000000000000000*60) f407desc9IntegerFormShared=f407desc9Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (60*1000000000000000000000000*60) f407desc9IntegerFormShared) (f407desc9Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 60
    f416rawInteger f407desc9IntegerCoordinatesShared f407desc9IntegerLeftProductShared f407desc9IntegerFormShared
    f416rawM4Form f407desc9 f407desc9Form f416_raw_integer_check hD hV hY hF

theorem f407desc9_source_form (x y : Fin 2 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[9] (natFourWordBlock f407basis (complexify b407relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[9]
          (natFourWordBlock f407basis (complexify b407relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f407desc9Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 9
    f407basis b407relative
    f416basis f407desc9 f416rawM4Form f407desc9Form
    f407desc9_actual f416_actual_raw_M4_matrix f407desc9_compression_check x y


#print axioms f407desc9_compression_check
#print axioms f407desc9_source_form
end TorusLean.BosonFiniteCertificate
