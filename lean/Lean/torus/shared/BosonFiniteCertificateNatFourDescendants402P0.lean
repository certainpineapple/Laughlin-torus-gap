import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates402
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger402
import torus.shared.BosonFiniteCertificateNatFourRaise402
import torus.shared.BosonFiniteCertificateNatFourRaise403
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
import torus.shared.BosonFiniteCertificate402

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

def f402desc0Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(3189110676006573669471421/250000000000000000000000)]

private def f402desc0IntegerCoordinates : Matrix (Fin 2) (Fin 1) ℤ :=
  !![(-1);
    1]

private def f402desc0IntegerLeftProduct : Matrix (Fin 1) (Fin 2) ℤ :=
  !![(-8310430425729839364143796), 4446012278296455313741888]

private def f402desc0IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![12756442704026294677885684]

theorem f402desc0_compression_check :
    f402desc0ᵀ*f402rawM4Form*f402desc0=f402desc0Form := by
  have hD : natFourIntegerMatrix 1 f402desc0IntegerCoordinates=f402desc0 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f402desc0IntegerCoordinates) (f402desc0) (by decide +kernel) a b
  have hV : f402desc0IntegerCoordinatesᵀ*f402rawInteger=f402desc0IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f402desc0IntegerCoordinatesᵀ*f402rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f402desc0IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f402desc0IntegerLeftProduct*f402desc0IntegerCoordinates=f402desc0IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc0IntegerLeftProduct*f402desc0IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc0IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc0IntegerForm=f402desc0Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc0IntegerForm) (f402desc0Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f402rawInteger f402desc0IntegerCoordinates f402desc0IntegerLeftProduct f402desc0IntegerForm
    f402rawM4Form f402desc0 f402desc0Form f402_raw_integer_check hD hV hY hF

theorem f402desc0_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0] (natFourWordBlock f402basis (complexify b402relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
          (natFourWordBlock f402basis (complexify b402relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f402desc0Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 0
    f402basis b402relative
    f402basis f402desc0 f402rawM4Form f402desc0Form
    f402desc0_actual f402_actual_raw_M4_matrix f402desc0_compression_check x y


#print axioms f402desc0_compression_check
#print axioms f402desc0_source_form
end TorusLean.BosonFiniteCertificate
