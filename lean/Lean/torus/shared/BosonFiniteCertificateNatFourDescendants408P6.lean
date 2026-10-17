import torus.shared.BosonFiniteCertificateNatFourDescendants408P6LeftRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants408P6LeftRow1
import torus.shared.BosonFiniteCertificateNatFourDescendants408P6LeftRow2
import torus.shared.BosonFiniteCertificateNatFourDescendants408P6LeftRow3

import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates408
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger414
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

private theorem f408desc6_coordinates_decode : natFourIntegerMatrix 210 f408desc6IntegerCoordinatesShared=f408desc6 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 210 f408desc6IntegerCoordinatesShared) (f408desc6) (by decide +kernel) a b

#print axioms f408desc6_coordinates_decode

theorem f408desc6_compression_check :
    f408desc6ᵀ*f414rawM4Form*f408desc6=f408desc6Form := by
  have hD := f408desc6_coordinates_decode
  have hV : f408desc6IntegerCoordinatesSharedᵀ*f414rawInteger=f408desc6IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f408desc6_integer_left_row0 b
    · exact f408desc6_integer_left_row1 b
    · exact f408desc6_integer_left_row2 b
    · exact f408desc6_integer_left_row3 b
  have hY : f408desc6IntegerLeftProductShared*f408desc6IntegerCoordinatesShared=f408desc6IntegerFormShared := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc6IntegerLeftProductShared*f408desc6IntegerCoordinatesShared) 0 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc6IntegerFormShared) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc6IntegerLeftProductShared*f408desc6IntegerCoordinatesShared) 1 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc6IntegerFormShared) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc6IntegerLeftProductShared*f408desc6IntegerCoordinatesShared) 2 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc6IntegerFormShared) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc6IntegerLeftProductShared*f408desc6IntegerCoordinatesShared) 3 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc6IntegerFormShared) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (210*1000000000000000000000000*210) f408desc6IntegerFormShared=f408desc6Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (210*1000000000000000000000000*210) f408desc6IntegerFormShared) (f408desc6Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 210
    f414rawInteger f408desc6IntegerCoordinatesShared f408desc6IntegerLeftProductShared f408desc6IntegerFormShared
    f414rawM4Form f408desc6 f408desc6Form f414_raw_integer_check hD hV hY hF

theorem f408desc6_source_form (x y : Fin 4 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6] (natFourWordBlock f408basis (complexify b408relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6]
          (natFourWordBlock f408basis (complexify b408relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f408desc6Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 6
    f408basis b408relative
    f414basis f408desc6 f414rawM4Form f408desc6Form
    f408desc6_actual f414_actual_raw_M4_matrix f408desc6_compression_check x y


#print axioms f408desc6_compression_check
#print axioms f408desc6_source_form
end TorusLean.BosonFiniteCertificate
