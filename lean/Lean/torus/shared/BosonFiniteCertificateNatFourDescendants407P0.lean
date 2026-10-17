import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates407
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger407
import torus.shared.BosonFiniteCertificateNatFourRaise407
import torus.shared.BosonFiniteCertificateNatFourRaise408
import torus.shared.BosonFiniteCertificateNatFourRaise409
import torus.shared.BosonFiniteCertificateNatFourRaise410
import torus.shared.BosonFiniteCertificateNatFourRaise411
import torus.shared.BosonFiniteCertificateNatFourRaise412
import torus.shared.BosonFiniteCertificateNatFourRaise413
import torus.shared.BosonFiniteCertificateNatFourRaise414
import torus.shared.BosonFiniteCertificateNatFourRaise415
import torus.shared.BosonFiniteCertificate407

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

def f407desc0Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(-2214645425378274108694598511/25000000000000000000000000), (22587106976670869967322491/195312500000000000000000);
    (22587106976670869967322491/195312500000000000000000), (-1961677260680900335062408911/14062500000000000000000000)]

private def f407desc0IntegerCoordinates : Matrix (Fin 11) (Fin 2) ℤ :=
  !![3, (-4);
    (-21), 28;
    27, (-16);
    (-15), 0;
    36, (-68);
    (-90), 80;
    60, 0;
    0, (-20);
    0, 60;
    0, (-120);
    0, 60]

private def f407desc0IntegerLeftProduct : Matrix (Fin 2) (Fin 11) ℤ :=
  !![(-6647386078899540413640031680), 2821653548128171744484416200, (-3012988668559699330980666432), 848112181871728703471787672, (-824948654170862736402786720), 1129260983557982264520520464, (-238467360958732816183789632), 30789246273845375436562152, 643659553267839891219469320, (-322745545214917787845972656), 655854209486907461648149032;
    8871322166603077767421783680, (-4380171306219370255626653280), 4518821438301874742294710656, (-1886172534028866199963699296), 1117652935004220231255278400, (-672488867989695238947561152), 777795353996222594922998016, 321366749318239635265443104, (-865517049395424717973061760), 553734660206930299846245088, (-285868738109021751093701376)]

private def f407desc0IntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(-318908941254471471652022185584), 416325555793997475237688154112;
    416325555793997475237688154112, (-502189378734310485775976681216)]

theorem f407desc0_compression_check :
    f407desc0ᵀ*f407rawM4Form*f407desc0=f407desc0Form := by
  have hD : natFourIntegerMatrix 60 f407desc0IntegerCoordinates=f407desc0 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 60 f407desc0IntegerCoordinates) (f407desc0) (by decide +kernel) a b
  have hV : f407desc0IntegerCoordinatesᵀ*f407rawInteger=f407desc0IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 11) => (f407desc0IntegerCoordinatesᵀ*f407rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 11) => (f407desc0IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 11) => (f407desc0IntegerCoordinatesᵀ*f407rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 11) => (f407desc0IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f407desc0IntegerLeftProduct*f407desc0IntegerCoordinates=f407desc0IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc0IntegerLeftProduct*f407desc0IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc0IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc0IntegerLeftProduct*f407desc0IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc0IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (60*1000000000000000000000000*60) f407desc0IntegerForm=f407desc0Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (60*1000000000000000000000000*60) f407desc0IntegerForm) (f407desc0Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 60
    f407rawInteger f407desc0IntegerCoordinates f407desc0IntegerLeftProduct f407desc0IntegerForm
    f407rawM4Form f407desc0 f407desc0Form f407_raw_integer_check hD hV hY hF

theorem f407desc0_source_form (x y : Fin 2 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0] (natFourWordBlock f407basis (complexify b407relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
          (natFourWordBlock f407basis (complexify b407relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f407desc0Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 0
    f407basis b407relative
    f407basis f407desc0 f407rawM4Form f407desc0Form
    f407desc0_actual f407_actual_raw_M4_matrix f407desc0_compression_check x y


#print axioms f407desc0_compression_check
#print axioms f407desc0_source_form
end TorusLean.BosonFiniteCertificate
