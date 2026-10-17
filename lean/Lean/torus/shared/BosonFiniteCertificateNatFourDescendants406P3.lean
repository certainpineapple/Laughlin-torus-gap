import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates406
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger409
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
import torus.shared.BosonFiniteCertificate406

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

def f406desc3Form : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(1053942163963740032136615729/156250000000000000000000), (-1236862228636797654561013017/312500000000000000000000), (-104069052873747823643999067/31250000000000000000000);
    (-1236862228636797654561013017/312500000000000000000000), (451981381235720808327949239/78125000000000000000000), (1543457245031020515720136259/312500000000000000000000);
    (-104069052873747823643999067/31250000000000000000000), (1543457245031020515720136259/312500000000000000000000), (2427703346811867354055095553/468750000000000000000000)]

private def f406desc3IntegerCoordinates : Matrix (Fin 18) (Fin 3) ℤ :=
  !![(-3), 3, 3;
    (-9), 9, 9;
    (-18), (-12), (-22);
    (-30), 0, (-30);
    18, 42, 2;
    54, (-24), (-14);
    0, (-60), (-20);
    (-36), (-24), 76;
    90, (-30), 50;
    (-162), 72, 102;
    0, 60, 20;
    60, 0, (-60);
    90, 0, (-10);
    (-54), 144, 54;
    90, (-240), (-170);
    (-270), 180, 30;
    180, (-240), (-260);
    0, 120, 240]

private def f406desc3IntegerLeftProduct : Matrix (Fin 3) (Fin 18) ℤ :=
  !![0, (-29400699279171284646872927040), 20421316313459106939848564928, 8350966455047379972540925920, 27747301249650544174576924992, 2721923552094405952025229120, (-2613652220856273577265904768), 9714520952851233020526740160, 16529818951212849158318041536, (-9644204364353402352133868640), 6780540080766648500824862016, 17945726659032446640296878464, (-12337858539753375637596568320), (-3498404895889667856483725952), 1647932795125895834446331232, (-4742980091446439693128148352), 8296039633220338981902470784, 3760606128145573928429229600;
    0, 3256861540993284005928685440, (-15674977750202207977891163328), 7637329589788500130488113280, 22888420534280649785076609408, (-6806940466372130600034707520), 626917662535367172415736448, (-9415846935217087818680201760), 2731240337936536348711043904, (-2346900561308320074200875680), (-8122792121804215441951742016), (-24059018617062034734346705344), (-2861104163433553950879732480), (-1640219214862546288328855808), (-9435729713092566158134530432), 226340272669679709728118912, (-11513787610737341341374249024), (-3481531144671952186003520640);
    0, (-578837384155287854789117760), (-4797137154962884077794708928), (-23241571541284556349677276640), 7799271319037569608352686528, (-7189294993454900847955398720), 6824436282801519036724693248, (-11943737368994256723759824640), 1338076302010929100437777984, (-695898162078424803276014880), (-8904328447054679085764169216), (-20641283917704563141946867264), (-3108917384562063852187390080), (-606224307003094576214738688), (-11992242653267809635619085472), (-914564344813693348084937088), (-10463237723764992836645873664), (-4144883195856595531278843360)]

private def f406desc3IntegerForm : Matrix (Fin 3) (Fin 3) ℤ :=
  !![6070706864431142585106906599040, (-3562163218473977245135717488960), (-2997188722763937320947173129600);
    (-3562163218473977245135717488960), 5206825511835503711937975233280, 4445156865689339085273992425920;
    (-2997188722763937320947173129600), 4445156865689339085273992425920, 4661190425878785319785783461760]

theorem f406desc3_compression_check :
    f406desc3ᵀ*f409rawM4Form*f406desc3=f406desc3Form := by
  have hD : natFourIntegerMatrix 30 f406desc3IntegerCoordinates=f406desc3 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 30 f406desc3IntegerCoordinates) (f406desc3) (by decide +kernel) a b
  have hV : f406desc3IntegerCoordinatesᵀ*f409rawInteger=f406desc3IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 18) => (f406desc3IntegerCoordinatesᵀ*f409rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 18) => (f406desc3IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 18) => (f406desc3IntegerCoordinatesᵀ*f409rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 18) => (f406desc3IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 18) => (f406desc3IntegerCoordinatesᵀ*f409rawInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 18) => (f406desc3IntegerLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f406desc3IntegerLeftProduct*f406desc3IntegerCoordinates=f406desc3IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc3IntegerLeftProduct*f406desc3IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc3IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc3IntegerLeftProduct*f406desc3IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc3IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc3IntegerLeftProduct*f406desc3IntegerCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc3IntegerForm) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (30*1000000000000000000000000*30) f406desc3IntegerForm=f406desc3Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (30*1000000000000000000000000*30) f406desc3IntegerForm) (f406desc3Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 30
    f409rawInteger f406desc3IntegerCoordinates f406desc3IntegerLeftProduct f406desc3IntegerForm
    f409rawM4Form f406desc3 f406desc3Form f409_raw_integer_check hD hV hY hF

theorem f406desc3_source_form (x y : Fin 3 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3] (natFourWordBlock f406basis (complexify b406relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
          (natFourWordBlock f406basis (complexify b406relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f406desc3Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 3
    f406basis b406relative
    f409basis f406desc3 f409rawM4Form f406desc3Form
    f406desc3_actual f409_actual_raw_M4_matrix f406desc3_compression_check x y


#print axioms f406desc3_compression_check
#print axioms f406desc3_source_form
end TorusLean.BosonFiniteCertificate
