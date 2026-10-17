import torus.shared.BosonFiniteCertificateNatFourDescendants408P8LeftRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants408P8LeftRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants408P8LeftRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants408P8LeftRow3

import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates408
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger416
import torus.shared.BosonFiniteCertificateNatFourRaise408
import torus.shared.BosonFiniteCertificateNatFourRaise409
import torus.shared.BosonFiniteCertificateNatFourRaise410
import torus.shared.BosonFiniteCertificateNatFourRaise411
import torus.shared.BosonFiniteCertificateNatFourRaise412
import torus.shared.BosonFiniteCertificateNatFourRaise413
import torus.shared.BosonFiniteCertificateNatFourRaise414
import torus.shared.BosonFiniteCertificateNatFourRaise415
import torus.shared.BosonFiniteCertificate408

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

private theorem f408desc8_coordinates_decode : natFourIntegerMatrix 210 f408desc8IntegerCoordinatesShared=f408desc8 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 210 f408desc8IntegerCoordinatesShared) (f408desc8) (by decide +kernel) a b

#print axioms f408desc8_coordinates_decode

theorem f408desc8_compression_check :
    f408desc8ᵀ*f416rawM4Form*f408desc8=f408desc8Form := by
  have hD := f408desc8_coordinates_decode
  have hV : f408desc8IntegerCoordinatesSharedᵀ*f416rawInteger=f408desc8IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f408desc8_integer_left_row0 b
    · exact f408desc8_integer_left_row1 b
    · exact f408desc8_integer_left_row2 b
    · exact f408desc8_integer_left_row3 b
  have hY : f408desc8IntegerLeftProductShared*f408desc8IntegerCoordinatesShared=f408desc8IntegerFormShared := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc8IntegerLeftProductShared*f408desc8IntegerCoordinatesShared) 0 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc8IntegerFormShared) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc8IntegerLeftProductShared*f408desc8IntegerCoordinatesShared) 1 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc8IntegerFormShared) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc8IntegerLeftProductShared*f408desc8IntegerCoordinatesShared) 2 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc8IntegerFormShared) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc8IntegerLeftProductShared*f408desc8IntegerCoordinatesShared) 3 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc8IntegerFormShared) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (210*1000000000000000000000000*210) f408desc8IntegerFormShared=f408desc8Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (210*1000000000000000000000000*210) f408desc8IntegerFormShared) (f408desc8Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 210
    f416rawInteger f408desc8IntegerCoordinatesShared f408desc8IntegerLeftProductShared f408desc8IntegerFormShared
    f416rawM4Form f408desc8 f408desc8Form f416_raw_integer_check hD hV hY hF

theorem f408desc8_source_form (x y : Fin 4 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8] (natFourWordBlock f408basis (complexify b408relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8]
          (natFourWordBlock f408basis (complexify b408relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f408desc8Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 8
    f408basis b408relative
    f416basis f408desc8 f416rawM4Form f408desc8Form
    f408desc8_actual f416_actual_raw_M4_matrix f408desc8_compression_check x y


#print axioms f408desc8_compression_check
#print axioms f408desc8_source_form
end TorusLean.BosonFiniteCertificate
