import torus.shared.BosonFiniteCertificateNatFourDescendants409P6LeftRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants409P6LeftRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants409P6LeftRow2

import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates409
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger415
import torus.shared.BosonFiniteCertificateNatFourRaise409
import torus.shared.BosonFiniteCertificateNatFourRaise410
import torus.shared.BosonFiniteCertificateNatFourRaise411
import torus.shared.BosonFiniteCertificateNatFourRaise412
import torus.shared.BosonFiniteCertificateNatFourRaise413
import torus.shared.BosonFiniteCertificateNatFourRaise414
import torus.shared.BosonFiniteCertificateNatFourRaise415
import torus.shared.BosonFiniteCertificate409

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

private theorem f409desc6_coordinates_decode : natFourIntegerMatrix 280 f409desc6IntegerCoordinatesShared=f409desc6 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 280 f409desc6IntegerCoordinatesShared) (f409desc6) (by decide +kernel) a b

#print axioms f409desc6_coordinates_decode

theorem f409desc6_compression_check :
    f409desc6ᵀ*f415rawM4Form*f409desc6=f409desc6Form := by
  have hD := f409desc6_coordinates_decode
  have hV : f409desc6IntegerCoordinatesSharedᵀ*f415rawInteger=f409desc6IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f409desc6_integer_left_row0 b
    · exact f409desc6_integer_left_row1 b
    · exact f409desc6_integer_left_row2 b
  have hY : f409desc6IntegerLeftProductShared*f409desc6IntegerCoordinatesShared=f409desc6IntegerFormShared := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc6IntegerLeftProductShared*f409desc6IntegerCoordinatesShared) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc6IntegerFormShared) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc6IntegerLeftProductShared*f409desc6IntegerCoordinatesShared) 1 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc6IntegerFormShared) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc6IntegerLeftProductShared*f409desc6IntegerCoordinatesShared) 2 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc6IntegerFormShared) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (280*1000000000000000000000000*280) f409desc6IntegerFormShared=f409desc6Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (280*1000000000000000000000000*280) f409desc6IntegerFormShared) (f409desc6Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 280
    f415rawInteger f409desc6IntegerCoordinatesShared f409desc6IntegerLeftProductShared f409desc6IntegerFormShared
    f415rawM4Form f409desc6 f409desc6Form f415_raw_integer_check hD hV hY hF

theorem f409desc6_source_form (x y : Fin 3 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6] (natFourWordBlock f409basis (complexify b409relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6]
          (natFourWordBlock f409basis (complexify b409relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f409desc6Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 6
    f409basis b409relative
    f415basis f409desc6 f415rawM4Form f409desc6Form
    f409desc6_actual f415_actual_raw_M4_matrix f409desc6_compression_check x y


#print axioms f409desc6_compression_check
#print axioms f409desc6_source_form
end TorusLean.BosonFiniteCertificate
