import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates402
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger412
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

def f402desc10Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1426412272865138234993941590663/1220703125000000000)]

private def f402desc10IntegerCoordinates : Matrix (Fin 34) (Fin 1) ℤ :=
  !![(-1);
    (-28);
    (-118);
    (-300);
    (-525);
    (-696);
    (-378);
    (-228);
    (-1640);
    (-3480);
    (-5040);
    (-5712);
    (-2430);
    (-8160);
    (-9240);
    (-4536);
    (-5040);
    (-8400);
    (-1050);
    (-520);
    (-4500);
    (-7200);
    (-7560);
    (-3528);
    (-9360);
    (-16800);
    (-5040);
    3360;
    12600;
    (-2520);
    15120;
    15750;
    58800;
    8400]

private def f402desc10IntegerLeftProduct : Matrix (Fin 1) (Fin 34) ℤ :=
  !![0, 0, 0, 0, (-29512943034359731087312016179200), (-145597658216552416395193490841600), (-247167228698497731615472636876800), 0, 0, 577962995714791696430984908800, (-18960937029648876433021848506880), (-70741806778316660754416811436800), 917213138751927042959773593600, 2265189167666286748209496320000, (-16122918880410482619183918804480), (-28589757585266870546189969779200), (-4587460361871451604324283801600), (-8855047915255520015138524972800), (-12457620249602886150767414507520), 0, 41055406604170952986053734400, 2054633682969337955420516313600, (-10535935797809923686284258818560), (-22345316007428010402676745510400), 2409715609220086910377510579200, (-2062943623450793310292375372800), (-6124833068449576078455918243840), (-2196385013964260641491606816000), (-1584080563660127899303650324480), (-3359033249844043519436904422400), (-2408765383039753158669053107200), (-5476085145309415994543213568000), 802082801754183721228932003840, 0]

private def f402desc10IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![1168516933931121242107036951071129600]

theorem f402desc10_compression_check :
    f402desc10ᵀ*f412rawM4Form*f402desc10=f402desc10Form := by
  have hD : natFourIntegerMatrix 1 f402desc10IntegerCoordinates=f402desc10 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f402desc10IntegerCoordinates) (f402desc10) (by decide +kernel) a b
  have hV : f402desc10IntegerCoordinatesᵀ*f412rawInteger=f402desc10IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f402desc10IntegerCoordinatesᵀ*f412rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f402desc10IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f402desc10IntegerLeftProduct*f402desc10IntegerCoordinates=f402desc10IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc10IntegerLeftProduct*f402desc10IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc10IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc10IntegerForm=f402desc10Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc10IntegerForm) (f402desc10Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f412rawInteger f402desc10IntegerCoordinates f402desc10IntegerLeftProduct f402desc10IntegerForm
    f412rawM4Form f402desc10 f402desc10Form f412_raw_integer_check hD hV hY hF

theorem f402desc10_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[10] (natFourWordBlock f402basis (complexify b402relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[10]
          (natFourWordBlock f402basis (complexify b402relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f402desc10Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 10
    f402basis b402relative
    f412basis f402desc10 f412rawM4Form f402desc10Form
    f402desc10_actual f412_actual_raw_M4_matrix f402desc10_compression_check x y


#print axioms f402desc10_compression_check
#print axioms f402desc10_source_form
end TorusLean.BosonFiniteCertificate
