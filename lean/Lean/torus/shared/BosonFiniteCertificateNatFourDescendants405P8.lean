import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates405
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger413
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
import torus.shared.BosonFiniteCertificate405

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

def f405desc8Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(11070170063947382851250108319/156250000000000000000)]

private def f405desc8IntegerCoordinates : Matrix (Fin 39) (Fin 1) ℤ :=
  !![(-1);
    (-19);
    (-46);
    (-46);
    3;
    51;
    60;
    (-96);
    (-316);
    (-64);
    326;
    256;
    28;
    (-38);
    916;
    1224;
    392;
    1088;
    1736;
    448;
    658;
    (-120);
    (-296);
    256;
    (-96);
    (-1456);
    474;
    1728;
    (-3192);
    (-3696);
    (-224);
    (-5824);
    (-1050);
    552;
    504;
    (-3108);
    1568;
    2940;
    4480]

private def f405desc8IntegerLeftProduct : Matrix (Fin 1) (Fin 39) ℤ :=
  !![0, 0, 0, 0, 0, (-4436944222745643110006985561600), 6322754641300366206369476620800, 0, 0, 0, 116330824151314962557592268800, 4444781509472748412645824883200, 2524897684126427458303520179200, 0, (-20676692998183463281784217600), 4793449258694868410694182400, 915629072324139990048269433600, (-650419869821382807786153561600), 310612377558894098643338803200, 147203735685879547320468940800, (-874234082819258461418511225600), 0, 0, 59047578337303724378537779200, (-198502988570335009909840665600), 988284166476461950105915603200, 3874907287286180667267379200, (-431778476146813266329001561600), 228851374418876611687057228800, (-227386288239724310199391872000), (-419340211947309786035906880000), (-199104560121464705911416710400), 0, (-9840644643213846551314713600), (-272508632906347940024156659200), (-687647248417567927697025081600), 174777286243027756569999840000, 0, 0]

private def f405desc8IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![2550567182733477008928024956697600]

theorem f405desc8_compression_check :
    f405desc8ᵀ*f413rawM4Form*f405desc8=f405desc8Form := by
  have hD : natFourIntegerMatrix 6 f405desc8IntegerCoordinates=f405desc8 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 6 f405desc8IntegerCoordinates) (f405desc8) (by decide +kernel) a b
  have hV : f405desc8IntegerCoordinatesᵀ*f413rawInteger=f405desc8IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f405desc8IntegerCoordinatesᵀ*f413rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f405desc8IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f405desc8IntegerLeftProduct*f405desc8IntegerCoordinates=f405desc8IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f405desc8IntegerLeftProduct*f405desc8IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f405desc8IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (6*1000000000000000000000000*6) f405desc8IntegerForm=f405desc8Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (6*1000000000000000000000000*6) f405desc8IntegerForm) (f405desc8Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 6
    f413rawInteger f405desc8IntegerCoordinates f405desc8IntegerLeftProduct f405desc8IntegerForm
    f413rawM4Form f405desc8 f405desc8Form f413_raw_integer_check hD hV hY hF

theorem f405desc8_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8] (natFourWordBlock f405basis (complexify b405relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8]
          (natFourWordBlock f405basis (complexify b405relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f405desc8Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 8
    f405basis b405relative
    f413basis f405desc8 f413rawM4Form f405desc8Form
    f405desc8_actual f413_actual_raw_M4_matrix f405desc8_compression_check x y


#print axioms f405desc8_compression_check
#print axioms f405desc8_source_form
end TorusLean.BosonFiniteCertificate
