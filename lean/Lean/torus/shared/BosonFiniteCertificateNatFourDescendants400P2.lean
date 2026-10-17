import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates400
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger402
import torus.shared.BosonFiniteCertificateNatFourRaise400
import torus.shared.BosonFiniteCertificateNatFourRaise401
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
import torus.shared.BosonFiniteCertificate400

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

def f400desc2Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(8759352134585162291873661/15625000000000000000000)]

private def f400desc2IntegerCoordinates : Matrix (Fin 2) (Fin 1) ℤ :=
  !![4;
    12]

private def f400desc2IntegerLeftProduct : Matrix (Fin 1) (Fin 2) ℤ :=
  !![19954589310862069436249040, 40065014947500175744576512]

private def f400desc2IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![560598536613450386679914304]

theorem f400desc2_compression_check :
    f400desc2ᵀ*f402rawM4Form*f400desc2=f400desc2Form := by
  have hD : natFourIntegerMatrix 1 f400desc2IntegerCoordinates=f400desc2 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f400desc2IntegerCoordinates) (f400desc2) (by decide +kernel) a b
  have hV : f400desc2IntegerCoordinatesᵀ*f402rawInteger=f400desc2IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f400desc2IntegerCoordinatesᵀ*f402rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f400desc2IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f400desc2IntegerLeftProduct*f400desc2IntegerCoordinates=f400desc2IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc2IntegerLeftProduct*f400desc2IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc2IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc2IntegerForm=f400desc2Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc2IntegerForm) (f400desc2Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f402rawInteger f400desc2IntegerCoordinates f400desc2IntegerLeftProduct f400desc2IntegerForm
    f402rawM4Form f400desc2 f400desc2Form f402_raw_integer_check hD hV hY hF

theorem f400desc2_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2] (natFourWordBlock f400basis (complexify b400relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
          (natFourWordBlock f400basis (complexify b400relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f400desc2Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 2
    f400basis b400relative
    f402basis f400desc2 f402rawM4Form f400desc2Form
    f400desc2_actual f402_actual_raw_M4_matrix f400desc2_compression_check x y


#print axioms f400desc2_compression_check
#print axioms f400desc2_source_form
end TorusLean.BosonFiniteCertificate
