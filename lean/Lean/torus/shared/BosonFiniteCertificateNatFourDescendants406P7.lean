import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates406
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger413
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

def f406desc7Form : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(205469634217771245644056853901/3906250000000000000000), (165935449234773403141886201889/3906250000000000000000), (-6589953195567725659890197133/1953125000000000000000);
    (165935449234773403141886201889/3906250000000000000000), (421725930581998022492997824121/3906250000000000000000), (6122501105571960166209730161/244140625000000000000);
    (-6589953195567725659890197133/1953125000000000000000), (6122501105571960166209730161/244140625000000000000), (98141365087208296044283502731/3906250000000000000000)]

private def f406desc7IntegerCoordinates : Matrix (Fin 39) (Fin 3) ℤ :=
  !![(-3), 3, 3;
    (-45), 45, 45;
    (-108), 78, 68;
    (-192), 42, (-28);
    (-255), 15, (-205);
    (-171), 171, (-249);
    12, 408, (-152);
    (-126), 156, 166;
    (-252), 192, 232;
    (-420), (-480), (-580);
    (-630), (-570), (-970);
    288, 552, (-8);
    588, 672, 392;
    0, (-330), (-140);
    (-1260), (-1320), (-440);
    (-1980), (-180), 1200;
    252, 1428, 3248;
    (-2040), 0, 840;
    (-2100), 2100, 2800;
    756, 1344, 1204;
    1890, 1470, (-350);
    126, 84, 114;
    1890, (-420), (-290);
    1890, (-1260), (-1170);
    1260, (-1440), (-660);
    2772, (-1512), 588;
    3780, (-630), (-780);
    0, 1200, 400;
    (-1260), (-2100), 560;
    2268, (-3528), (-588);
    (-4200), 1680, (-280);
    5040, (-9240), (-14840);
    3150, (-3150), (-5250);
    0, 1920, 840;
    (-10080), 10080, 5880;
    (-3780), 0, 840;
    (-7560), 6720, 4760;
    6300, (-4200), (-1400);
    4200, 0, 4200]

private def f406desc7IntegerLeftProduct : Matrix (Fin 3) (Fin 39) ℤ :=
  !![0, 0, 0, 0, 0, 23704388505580188113236832832000, 72207562576193878932707407142400, 0, 0, 0, 6990809668628862127584153600, 9471761683712724734629476595200, 22941174763946774967560460057600, 0, (-1242549979309615302389145600), 379062338593965622465594636800, 3749108273624058383847037881600, (-149358275384094059395392000), (-1025447811083184423440096870400), 915067490128856459427437568000, (-131497253356358718596644588800), 0, 0, 3548417783233989303261388800, 1456836632552915661545914752000, 2159281598316646363593913670400, 232860930791068790493696000, (-308006388445897650939087168000), (-1636335182885386432589407872000), 587219978396994312049980134400, (-1916757129219640602682820083200), (-221901377663244726822854419200), 0, (-1693637712575361246899099059200), (-862810110730796574710254348800), (-460832848512809817380335660800), (-387313216953764751917816774400), 0, 0;
    0, 0, 0, 0, 0, 42975244126913946744850001856000, 120546806493325948275794816217600, 0, 0, 0, 205599760779821859939556454400, 22059595142500156236716472460800, 34846339095427128407927419622400, 0, (-36543394424915328803082854400), 432791032763666993432174323200, 8570110438754696981446835270400, (-1537744139210717560463205312000), 1290263667184786039507730534400, 1377931496071582870316103168000, (-19279757283417661551181459200), 0, 0, 104358997120218467713009459200, 1931999913992379303855457920000, 5824118627057200052780341689600, 6848399029099562886034944000, (-514477793222056374980036544000), 1027241321606002668716731008000, 931812015101335449257749017600, (-1547357214835067264200416268800), 205746989564106228539909779200, 0, (-990420328462107499920151372800), 1018411778705307682212752140800, (-100112278342678870526941651200), 347974208989968730093326662400, 0, 0;
    0, 0, 0, 0, 0, (-27986306852049562978926706368000), 16306742281874744042550804441600, 0, 0, 0, (-195884050173878611658005401600), 100099009095728738290753420800, 11861736420590691149803097318400, 0, 34816527481149552174046617600, 1834423462909033842186910195200, 2425275114240719242355922374400, 1410197489869807769030510400000, 695075661285450834450015590400, (-823562047466796112130191104000), 742452336930981678576969196800, 0, 0, (-99427464317184419626295500800), 1303214596687646797981309056000, 461528040367702638876627129600, (-6524773537379129487641088000), 467638039378434052812979008000, 11844924827512858739432064000, (-1084511937935348077997760998400), (-230168509041199932639824140800), 359077163462085161883273235200, 0, 56287455108447380801048755200, 838456898327152581326951692800, 440493148274535292751424172800, 187592920039914758991513158400, 0, 0]

private def f406desc7IntegerForm : Matrix (Fin 3) (Fin 3) ℤ :=
  !![47340203723774494996390699138790400, 38231527503691792083890580915225600, (-3036650432517607984077402838886400);
    38231527503691792083890580915225600, 97165654406092344382386698677478400, 22569988075580473956715549265510400;
    (-3036650432517607984077402838886400), 22569988075580473956715549265510400, 22611770516092791408602919029222400]

theorem f406desc7_compression_check :
    f406desc7ᵀ*f413rawM4Form*f406desc7=f406desc7Form := by
  have hD : natFourIntegerMatrix 30 f406desc7IntegerCoordinates=f406desc7 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 30 f406desc7IntegerCoordinates) (f406desc7) (by decide +kernel) a b
  have hV : f406desc7IntegerCoordinatesᵀ*f413rawInteger=f406desc7IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f406desc7IntegerCoordinatesᵀ*f413rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f406desc7IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f406desc7IntegerCoordinatesᵀ*f413rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f406desc7IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f406desc7IntegerCoordinatesᵀ*f413rawInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f406desc7IntegerLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f406desc7IntegerLeftProduct*f406desc7IntegerCoordinates=f406desc7IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc7IntegerLeftProduct*f406desc7IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc7IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc7IntegerLeftProduct*f406desc7IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc7IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc7IntegerLeftProduct*f406desc7IntegerCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc7IntegerForm) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (30*1000000000000000000000000*30) f406desc7IntegerForm=f406desc7Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (30*1000000000000000000000000*30) f406desc7IntegerForm) (f406desc7Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 30
    f413rawInteger f406desc7IntegerCoordinates f406desc7IntegerLeftProduct f406desc7IntegerForm
    f413rawM4Form f406desc7 f406desc7Form f413_raw_integer_check hD hV hY hF

theorem f406desc7_source_form (x y : Fin 3 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7] (natFourWordBlock f406basis (complexify b406relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7]
          (natFourWordBlock f406basis (complexify b406relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f406desc7Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 7
    f406basis b406relative
    f413basis f406desc7 f413rawM4Form f406desc7Form
    f406desc7_actual f413_actual_raw_M4_matrix f406desc7_compression_check x y


#print axioms f406desc7_compression_check
#print axioms f406desc7_source_form
end TorusLean.BosonFiniteCertificate
