import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates400
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger413
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

def f400desc13Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(121866512127907986136491745699154979/2441406250000000000)]

private def f400desc13IntegerCoordinates : Matrix (Fin 39) (Fin 1) ℤ :=
  !![4;
    156;
    936;
    3432;
    8580;
    15444;
    20592;
    1872;
    20592;
    68640;
    154440;
    247104;
    144144;
    51480;
    308880;
    617760;
    864864;
    411840;
    1441440;
    864864;
    1081080;
    6864;
    102960;
    308880;
    617760;
    864864;
    463320;
    2471040;
    4324320;
    2594592;
    2882880;
    8648640;
    1801800;
    617760;
    4324320;
    6486480;
    8648640;
    10810800;
    4804800]

private def f400desc13IntegerLeftProduct : Matrix (Fin 1) (Fin 39) ℤ :=
  !![0, 0, 0, 0, 0, (-631510126392367669257558205286400), 32576739780165888806571652112332800, 0, 0, 0, 53886852906203958733334469427200, 363020312837663229845744803584000, 11390020799747083174005726986956800, 0, (-9577876633279437896648537702400), 1274162787002813383225626851174400, 4328366835671210759804741987251200, 366485745657203748093874990233600, 1090077945089008862456448412262400, (-1015854365252820383411925257625600), 2739491187114106209793921373260800, 0, 0, 27352067230121500215585460224000, 1231548847718053475435571242496000, 2564957389300632128159430089702400, 1794936121230147598298179584000, 493332237812971403495342607513600, 663055328399429701551881630822400, (-413895780342475268875561081958400), 1318542024127670948786355044812800, 875398492924530854586698641536000, 0, 662792669253498966686865833472000, 1652244558783455608866063366912000, 2179062080404918222515917523379200, 13990093760170310040512703820800, 0, 0]

private def f400desc13IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![49916523367591111121507019038373879398400]

theorem f400desc13_compression_check :
    f400desc13ᵀ*f413rawM4Form*f400desc13=f400desc13Form := by
  have hD : natFourIntegerMatrix 1 f400desc13IntegerCoordinates=f400desc13 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f400desc13IntegerCoordinates) (f400desc13) (by decide +kernel) a b
  have hV : f400desc13IntegerCoordinatesᵀ*f413rawInteger=f400desc13IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f400desc13IntegerCoordinatesᵀ*f413rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f400desc13IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f400desc13IntegerLeftProduct*f400desc13IntegerCoordinates=f400desc13IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc13IntegerLeftProduct*f400desc13IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc13IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc13IntegerForm=f400desc13Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc13IntegerForm) (f400desc13Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f413rawInteger f400desc13IntegerCoordinates f400desc13IntegerLeftProduct f400desc13IntegerForm
    f413rawM4Form f400desc13 f400desc13Form f413_raw_integer_check hD hV hY hF

theorem f400desc13_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[13] (natFourWordBlock f400basis (complexify b400relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[13]
          (natFourWordBlock f400basis (complexify b400relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f400desc13Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 13
    f400basis b400relative
    f413basis f400desc13 f413rawM4Form f400desc13Form
    f400desc13_actual f413_actual_raw_M4_matrix f400desc13_compression_check x y


#print axioms f400desc13_compression_check
#print axioms f400desc13_source_form
end TorusLean.BosonFiniteCertificate
