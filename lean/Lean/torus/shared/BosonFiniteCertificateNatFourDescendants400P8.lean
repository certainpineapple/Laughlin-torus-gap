import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates400
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger408
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

def f400desc8Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(17965464622555448381142584601/381469726562500000)]

private def f400desc8IntegerCoordinates : Matrix (Fin 15) (Fin 1) ℤ :=
  !![4;
    96;
    336;
    672;
    420;
    672;
    4032;
    6720;
    5040;
    6720;
    1344;
    10080;
    6720;
    20160;
    2520]

private def f400desc8IntegerLeftProduct : Matrix (Fin 1) (Fin 15) ℤ :=
  !![(-106062407074247349571282483200), 168100632843368240789772929280, 1134377432053327731683493142272, 179359918092617731795441984896, 341994762193070123494189443072, 18681637585876923489988446720, 321993381322821629664668233728, 1029930066168237840770185383936, 866106807416844989545100316672, 1053388715528153121893216856576, 137038714838195935815578880, 572333665473222092827319628288, 1121209664304364657500283126272, 633292891598812149690635188224, 272786755430819353200128741376]

private def f400desc8IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![47095387580151754604262416976445440]

theorem f400desc8_compression_check :
    f400desc8ᵀ*f408rawM4Form*f400desc8=f400desc8Form := by
  have hD : natFourIntegerMatrix 1 f400desc8IntegerCoordinates=f400desc8 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f400desc8IntegerCoordinates) (f400desc8) (by decide +kernel) a b
  have hV : f400desc8IntegerCoordinatesᵀ*f408rawInteger=f400desc8IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 15) => (f400desc8IntegerCoordinatesᵀ*f408rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 15) => (f400desc8IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f400desc8IntegerLeftProduct*f400desc8IntegerCoordinates=f400desc8IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc8IntegerLeftProduct*f400desc8IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc8IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc8IntegerForm=f400desc8Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc8IntegerForm) (f400desc8Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f408rawInteger f400desc8IntegerCoordinates f400desc8IntegerLeftProduct f400desc8IntegerForm
    f408rawM4Form f400desc8 f400desc8Form f408_raw_integer_check hD hV hY hF

theorem f400desc8_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8] (natFourWordBlock f400basis (complexify b400relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8]
          (natFourWordBlock f400basis (complexify b400relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f400desc8Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 8
    f400basis b400relative
    f408basis f400desc8 f408rawM4Form f400desc8Form
    f400desc8_actual f408_actual_raw_M4_matrix f400desc8_compression_check x y


#print axioms f400desc8_compression_check
#print axioms f400desc8_source_form
end TorusLean.BosonFiniteCertificate
