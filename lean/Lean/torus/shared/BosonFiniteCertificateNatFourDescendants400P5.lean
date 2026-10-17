import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates400
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger405
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

def f400desc5Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(8276432794146474060833810289/3125000000000000000000)]

private def f400desc5IntegerCoordinates : Matrix (Fin 6) (Fin 1) ℤ :=
  !![4;
    60;
    120;
    240;
    360;
    240]

private def f400desc5IntegerLeftProduct : Matrix (Fin 1) (Fin 6) ℤ :=
  !![254737253416488608668109760, (-574140134307301749123968784), 913779156573534747809889696, 1536333113303516562160371168, 3894217781940574056950657664, 3339983773714037686756968240]

private def f400desc5IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![2648458494126871699466819292480]

theorem f400desc5_compression_check :
    f400desc5ᵀ*f405rawM4Form*f400desc5=f400desc5Form := by
  have hD : natFourIntegerMatrix 1 f400desc5IntegerCoordinates=f400desc5 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f400desc5IntegerCoordinates) (f400desc5) (by decide +kernel) a b
  have hV : f400desc5IntegerCoordinatesᵀ*f405rawInteger=f400desc5IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 6) => (f400desc5IntegerCoordinatesᵀ*f405rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 6) => (f400desc5IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f400desc5IntegerLeftProduct*f400desc5IntegerCoordinates=f400desc5IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc5IntegerLeftProduct*f400desc5IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc5IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc5IntegerForm=f400desc5Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc5IntegerForm) (f400desc5Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f405rawInteger f400desc5IntegerCoordinates f400desc5IntegerLeftProduct f400desc5IntegerForm
    f405rawM4Form f400desc5 f400desc5Form f405_raw_integer_check hD hV hY hF

theorem f400desc5_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5] (natFourWordBlock f400basis (complexify b400relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
          (natFourWordBlock f400basis (complexify b400relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f400desc5Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 5
    f400basis b400relative
    f405basis f400desc5 f405rawM4Form f400desc5Form
    f400desc5_actual f405_actual_raw_M4_matrix f400desc5_compression_check x y


#print axioms f400desc5_compression_check
#print axioms f400desc5_source_form
end TorusLean.BosonFiniteCertificate
