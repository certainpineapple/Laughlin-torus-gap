import torus.shared.BosonFiniteCertificateNatFourDescendants404P12LeftRow0
import torus.shared.BosonFiniteCertificateNatFourDescendants404P12LeftRow1

import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates404
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger416
import torus.shared.BosonFiniteCertificateNatFourRaise404
import torus.shared.BosonFiniteCertificateNatFourRaise405
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
import torus.shared.BosonFiniteCertificate404

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

private theorem f404desc12_coordinates_decode : natFourIntegerMatrix 3 f404desc12IntegerCoordinatesShared=f404desc12 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 3 f404desc12IntegerCoordinatesShared) (f404desc12) (by decide +kernel) a b

#print axioms f404desc12_coordinates_decode

theorem f404desc12_compression_check :
    f404desc12ᵀ*f416rawM4Form*f404desc12=f404desc12Form := by
  have hD := f404desc12_coordinates_decode
  have hV : f404desc12IntegerCoordinatesSharedᵀ*f416rawInteger=f404desc12IntegerLeftProductShared := by
    ext a b
    fin_cases a
    · exact f404desc12_integer_left_row0 b
    · exact f404desc12_integer_left_row1 b
  have hY : f404desc12IntegerLeftProductShared*f404desc12IntegerCoordinatesShared=f404desc12IntegerFormShared := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc12IntegerLeftProductShared*f404desc12IntegerCoordinatesShared) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc12IntegerFormShared) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc12IntegerLeftProductShared*f404desc12IntegerCoordinatesShared) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc12IntegerFormShared) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc12IntegerFormShared=f404desc12Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc12IntegerFormShared) (f404desc12Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 3
    f416rawInteger f404desc12IntegerCoordinatesShared f404desc12IntegerLeftProductShared f404desc12IntegerFormShared
    f416rawM4Form f404desc12 f404desc12Form f416_raw_integer_check hD hV hY hF

theorem f404desc12_source_form (x y : Fin 2 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[12] (natFourWordBlock f404basis (complexify b404relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[12]
          (natFourWordBlock f404basis (complexify b404relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f404desc12Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 12
    f404basis b404relative
    f416basis f404desc12 f416rawM4Form f404desc12Form
    f404desc12_actual f416_actual_raw_M4_matrix f404desc12_compression_check x y


#print axioms f404desc12_compression_check
#print axioms f404desc12_source_form
end TorusLean.BosonFiniteCertificate
