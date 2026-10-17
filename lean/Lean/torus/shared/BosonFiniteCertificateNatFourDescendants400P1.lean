import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates400
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger401
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

def f400desc1Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(820709680938658934797593/15625000000000000000000)]

private def f400desc1IntegerCoordinates : Matrix (Fin 1) (Fin 1) ℤ :=
  !![4]

private def f400desc1IntegerLeftProduct : Matrix (Fin 1) (Fin 1) ℤ :=
  !![13131354895018542956761488]

private def f400desc1IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![52525419580074171827045952]

theorem f400desc1_compression_check :
    f400desc1ᵀ*f401rawM4Form*f400desc1=f400desc1Form := by
  have hD : natFourIntegerMatrix 1 f400desc1IntegerCoordinates=f400desc1 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f400desc1IntegerCoordinates) (f400desc1) (by decide +kernel) a b
  have hV : f400desc1IntegerCoordinatesᵀ*f401rawInteger=f400desc1IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc1IntegerCoordinatesᵀ*f401rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc1IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f400desc1IntegerLeftProduct*f400desc1IntegerCoordinates=f400desc1IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc1IntegerLeftProduct*f400desc1IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc1IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc1IntegerForm=f400desc1Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc1IntegerForm) (f400desc1Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f401rawInteger f400desc1IntegerCoordinates f400desc1IntegerLeftProduct f400desc1IntegerForm
    f401rawM4Form f400desc1 f400desc1Form f401_raw_integer_check hD hV hY hF

theorem f400desc1_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1] (natFourWordBlock f400basis (complexify b400relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
          (natFourWordBlock f400basis (complexify b400relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f400desc1Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 1
    f400basis b400relative
    f401basis f400desc1 f401rawM4Form f400desc1Form
    f400desc1_actual f401_actual_raw_M4_matrix f400desc1_compression_check x y


#print axioms f400desc1_compression_check
#print axioms f400desc1_source_form
end TorusLean.BosonFiniteCertificate
