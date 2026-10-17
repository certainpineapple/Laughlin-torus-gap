import torus.shared.BosonFiniteCertificateNatFourDescendants409P7LeftRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants409P7LeftRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants409P7LeftRow2

import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates409
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger416
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

private theorem f409desc7_coordinates_decode : natFourIntegerMatrix 280 f409desc7IntegerCoordinatesShared=f409desc7 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 280 f409desc7IntegerCoordinatesShared) (f409desc7) (by decide +kernel) a b

#print axioms f409desc7_coordinates_decode

theorem f409desc7_compression_check :
    f409desc7ᵀ*f416rawM4Form*f409desc7=f409desc7Form := by
  have hD := f409desc7_coordinates_decode
  have hV : f409desc7IntegerCoordinatesSharedᵀ*f416rawInteger=f409desc7IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f409desc7_integer_left_row0 b
    · exact f409desc7_integer_left_row1 b
    · exact f409desc7_integer_left_row2 b
  have hY : f409desc7IntegerLeftProductShared*f409desc7IntegerCoordinatesShared=f409desc7IntegerFormShared := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc7IntegerLeftProductShared*f409desc7IntegerCoordinatesShared) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc7IntegerFormShared) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc7IntegerLeftProductShared*f409desc7IntegerCoordinatesShared) 1 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc7IntegerFormShared) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc7IntegerLeftProductShared*f409desc7IntegerCoordinatesShared) 2 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc7IntegerFormShared) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (280*1000000000000000000000000*280) f409desc7IntegerFormShared=f409desc7Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (280*1000000000000000000000000*280) f409desc7IntegerFormShared) (f409desc7Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 280
    f416rawInteger f409desc7IntegerCoordinatesShared f409desc7IntegerLeftProductShared f409desc7IntegerFormShared
    f416rawM4Form f409desc7 f409desc7Form f416_raw_integer_check hD hV hY hF

theorem f409desc7_source_form (x y : Fin 3 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7] (natFourWordBlock f409basis (complexify b409relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7]
          (natFourWordBlock f409basis (complexify b409relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f409desc7Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 7
    f409basis b409relative
    f416basis f409desc7 f416rawM4Form f409desc7Form
    f409desc7_actual f416_actual_raw_M4_matrix f409desc7_compression_check x y


#print axioms f409desc7_compression_check
#print axioms f409desc7_source_form
end TorusLean.BosonFiniteCertificate
