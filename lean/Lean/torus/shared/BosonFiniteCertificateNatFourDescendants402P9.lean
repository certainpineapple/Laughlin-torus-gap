import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates402
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger411
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

def f402desc9Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(170745909378604491596786895352257/1953125000000000000000)]

private def f402desc9IntegerCoordinates : Matrix (Fin 27) (Fin 1) ℤ :=
  !![(-1);
    (-25);
    (-93);
    (-207);
    (-318);
    (-378);
    (-178);
    (-1098);
    (-1968);
    (-2436);
    (-1260);
    (-1332);
    (-3528);
    (-3276);
    (-1512);
    (-1050);
    (-342);
    (-2376);
    (-2856);
    (-2268);
    (-3276);
    (-1008);
    1890;
    5880;
    756;
    13860;
    8400]

private def f402desc9IntegerLeftProduct : Matrix (Fin 1) (Fin 27) ℤ :=
  !![0, 0, 0, (-11897330690296175195839777954560), (-9235757279294646065981435210112), (-31080351801504775277037645377280), 0, 112148495265927205894694860800, (-1381178986150762174250549687040), (-3624327948410553701055900310272), (-16191248339638219542564641362560), 403778012595997015513012371840, (-1036763427376580862637463351040), (-5352877801281130782012398416320), (-2206634885265485218785050321280), (-1979727566111717441295304834560), 65220225869954718713370931200, 392335295099424962372633306880, (-515358210193173689584419400320), (-4217943130930797190716891379392), (-171283757143737142228291367040), (-1288659889457394359336611090560), (-412170398792992109091138941952), (-68745884312928725478703584000), (-1084679313906260367920966152320), (-231460788866195899100224675584), 672077123768423175621622151040]

private def f402desc9IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![87421905601845499697554890420355584]

theorem f402desc9_compression_check :
    f402desc9ᵀ*f411rawM4Form*f402desc9=f402desc9Form := by
  have hD : natFourIntegerMatrix 1 f402desc9IntegerCoordinates=f402desc9 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f402desc9IntegerCoordinates) (f402desc9) (by decide +kernel) a b
  have hV : f402desc9IntegerCoordinatesᵀ*f411rawInteger=f402desc9IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f402desc9IntegerCoordinatesᵀ*f411rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f402desc9IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f402desc9IntegerLeftProduct*f402desc9IntegerCoordinates=f402desc9IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc9IntegerLeftProduct*f402desc9IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc9IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc9IntegerForm=f402desc9Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc9IntegerForm) (f402desc9Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f411rawInteger f402desc9IntegerCoordinates f402desc9IntegerLeftProduct f402desc9IntegerForm
    f411rawM4Form f402desc9 f402desc9Form f411_raw_integer_check hD hV hY hF

theorem f402desc9_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[9] (natFourWordBlock f402basis (complexify b402relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[9]
          (natFourWordBlock f402basis (complexify b402relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f402desc9Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 9
    f402basis b402relative
    f411basis f402desc9 f411rawM4Form f402desc9Form
    f402desc9_actual f411_actual_raw_M4_matrix f402desc9_compression_check x y


#print axioms f402desc9_compression_check
#print axioms f402desc9_source_form
end TorusLean.BosonFiniteCertificate
