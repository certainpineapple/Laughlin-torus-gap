import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates400
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger410
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

def f400desc10Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(180528617849328569915084790600507/4882812500000000000)]

private def f400desc10IntegerCoordinates : Matrix (Fin 23) (Fin 1) ℤ :=
  !![4;
    120;
    540;
    1440;
    2520;
    1512;
    1080;
    8640;
    20160;
    30240;
    15120;
    60480;
    37800;
    50400;
    2880;
    30240;
    60480;
    37800;
    90720;
    302400;
    67200;
    75600;
    151200]

private def f400desc10IntegerLeftProduct : Matrix (Fin 1) (Fin 23) ℤ :=
  !![0, 0, 50422956206038124154158303216640, 59350764192508165667776917096960, 83808762531055258364696715333120, 115078317796645470729149194368000, 63648338803718481436680806400, 5049760016986066182474804211200, 19926565864157693516507914959360, 105552408410296966602438619610880, 12369049278319561162316686755840, 46329591286969538209435592421120, 82849386474489634022831851330560, 50363621290781795001981091553280, 846031948780998722125444992000, 6180805308917947070606212131840, 50301290181666841366909282375680, 75073460412799146527505684910080, 33535027723681018564173869875200, 37187413151951001637816907811840, 16411109505123507386215656683520, 29365674210993429720416132213760, 3293617117510782527989885885440]

private def f400desc10IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![36972260935542491118609365114983833600]

theorem f400desc10_compression_check :
    f400desc10ᵀ*f410rawM4Form*f400desc10=f400desc10Form := by
  have hD : natFourIntegerMatrix 1 f400desc10IntegerCoordinates=f400desc10 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f400desc10IntegerCoordinates) (f400desc10) (by decide +kernel) a b
  have hV : f400desc10IntegerCoordinatesᵀ*f410rawInteger=f400desc10IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f400desc10IntegerCoordinatesᵀ*f410rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f400desc10IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f400desc10IntegerLeftProduct*f400desc10IntegerCoordinates=f400desc10IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc10IntegerLeftProduct*f400desc10IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc10IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc10IntegerForm=f400desc10Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc10IntegerForm) (f400desc10Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f410rawInteger f400desc10IntegerCoordinates f400desc10IntegerLeftProduct f400desc10IntegerForm
    f410rawM4Form f400desc10 f400desc10Form f410_raw_integer_check hD hV hY hF

theorem f400desc10_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[10] (natFourWordBlock f400basis (complexify b400relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[10]
          (natFourWordBlock f400basis (complexify b400relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f400desc10Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 10
    f400basis b400relative
    f410basis f400desc10 f410rawM4Form f400desc10Form
    f400desc10_actual f410_actual_raw_M4_matrix f400desc10_compression_check x y


#print axioms f400desc10_compression_check
#print axioms f400desc10_source_form
end TorusLean.BosonFiniteCertificate
