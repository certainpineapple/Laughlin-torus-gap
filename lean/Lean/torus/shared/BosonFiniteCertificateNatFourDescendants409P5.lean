import torus.shared.BosonFiniteCertificateNatFourDescendants409P5LeftRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants409P5LeftRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants409P5LeftRow2

import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates409
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger414
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

private theorem f409desc5_coordinates_decode : natFourIntegerMatrix 280 f409desc5IntegerCoordinatesShared=f409desc5 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 280 f409desc5IntegerCoordinatesShared) (f409desc5) (by decide +kernel) a b

#print axioms f409desc5_coordinates_decode

theorem f409desc5_compression_check :
    f409desc5ᵀ*f414rawM4Form*f409desc5=f409desc5Form := by
  have hD := f409desc5_coordinates_decode
  have hV : f409desc5IntegerCoordinatesSharedᵀ*f414rawInteger=f409desc5IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f409desc5_integer_left_row0 b
    · exact f409desc5_integer_left_row1 b
    · exact f409desc5_integer_left_row2 b
  have hY : f409desc5IntegerLeftProductShared*f409desc5IntegerCoordinatesShared=f409desc5IntegerFormShared := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc5IntegerLeftProductShared*f409desc5IntegerCoordinatesShared) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc5IntegerFormShared) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc5IntegerLeftProductShared*f409desc5IntegerCoordinatesShared) 1 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc5IntegerFormShared) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc5IntegerLeftProductShared*f409desc5IntegerCoordinatesShared) 2 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc5IntegerFormShared) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (280*1000000000000000000000000*280) f409desc5IntegerFormShared=f409desc5Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (280*1000000000000000000000000*280) f409desc5IntegerFormShared) (f409desc5Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 280
    f414rawInteger f409desc5IntegerCoordinatesShared f409desc5IntegerLeftProductShared f409desc5IntegerFormShared
    f414rawM4Form f409desc5 f409desc5Form f414_raw_integer_check hD hV hY hF

theorem f409desc5_source_form (x y : Fin 3 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5] (natFourWordBlock f409basis (complexify b409relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
          (natFourWordBlock f409basis (complexify b409relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f409desc5Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 5
    f409basis b409relative
    f414basis f409desc5 f414rawM4Form f409desc5Form
    f409desc5_actual f414_actual_raw_M4_matrix f409desc5_compression_check x y


#print axioms f409desc5_compression_check
#print axioms f409desc5_source_form
end TorusLean.BosonFiniteCertificate
