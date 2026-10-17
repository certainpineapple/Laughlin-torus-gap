import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates408
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger411
import torus.shared.BosonFiniteCertificateNatFourRaise408
import torus.shared.BosonFiniteCertificateNatFourRaise409
import torus.shared.BosonFiniteCertificateNatFourRaise410
import torus.shared.BosonFiniteCertificateNatFourRaise411
import torus.shared.BosonFiniteCertificateNatFourRaise412
import torus.shared.BosonFiniteCertificateNatFourRaise413
import torus.shared.BosonFiniteCertificateNatFourRaise414
import torus.shared.BosonFiniteCertificateNatFourRaise415
import torus.shared.BosonFiniteCertificate408

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

def f408desc3Form : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(131847079761038147742023391/2734375000000000000000), (-23184480070578285183086937207/1093750000000000000000000), (-19132779827676644416944523431/1093750000000000000000000), (107452266129310185190629/5468750000000000000);
    (-23184480070578285183086937207/1093750000000000000000000), (2782770109946886753558749763/136718750000000000000000), (14016994422263361570790241163/1093750000000000000000000), (-5718554366666994461498215269/218750000000000000000000);
    (-19132779827676644416944523431/1093750000000000000000000), (14016994422263361570790241163/1093750000000000000000000), (50885606017268562794999216211/5468750000000000000000000), (-87519007523724443199149607159/5468750000000000000000000);
    (107452266129310185190629/5468750000000000000), (-5718554366666994461498215269/218750000000000000000000), (-87519007523724443199149607159/5468750000000000000000000), (12739289817601964509949074241/341796875000000000000000)]

private def f408desc3IntegerCoordinates : Matrix (Fin 27) (Fin 4) ℤ :=
  !![6, (-6), (-6), 10;
    6, (-6), (-6), 10;
    78, 27, 48, (-94);
    42, (-42), 21, (-42);
    (-132), (-78), (-15), 88;
    84, 21, 42, 56;
    (-180), 75, 54, (-76);
    252, 63, (-63), 84;
    (-384), (-36), (-288), 368;
    (-504), 189, (-105), (-224);
    504, 126, 0, (-336);
    720, (-90), (-153), 332;
    (-672), 42, 420, (-392);
    504, (-819), (-63), (-224);
    (-672), 252, 294, (-168);
    420, 210, (-420), 840;
    (-252), (-63), 0, 28;
    432, (-432), (-180), 272;
    (-1008), 588, 420, (-448);
    504, 126, 126, 560;
    1008, 252, 315, (-812);
    (-2016), 756, 756, (-1120);
    1260, (-1575), (-945), 1960;
    0, 840, 630, (-2520);
    0, 0, (-567), 588;
    0, (-1260), (-1575), 2940;
    0, 840, 1260, (-1680)]

private def f408desc3IntegerLeftProduct : Matrix (Fin 4) (Fin 27) ℤ :=
  !![0, 0, 0, 1462757242275304418128156208640, (-113021726079924676260095705856), 2278304173696230324204680332800, 0, 23777067309786720368410890240, 99753520863224763474607342080, 805776322080706379251420276224, 1898673867747275818061783796480, 221410723332436099612720899840, 27563565322847521003300692480, 846773733931003221035057230464, 59753027560459048581311712000, 384403512998943187851834920448, 13827610380052671809782210560, 75623499409500564647897479680, 154429050848907146198240643840, 442671123474637471869862787712, (-186014464768652025659603016960), (-136778022200382871426007420160), 370126802297233250735976474624, 61033626410734923754422145536, 42872478450675668717006580480, 84079806503248565244481360896, (-33449989530628568512901502720);
    0, 0, 0, (-839366446429490187922554133440), (-782506600798967362338031597824), (-506657818083218135886456307200), 0, 4705877674333727071777013760, 35840090313214769467171782720, (-312864799924359348948878033664), 114580601352106197792118686720, 36878567223704995628890767360, (-39795680678293906587290263680), (-249315441538147747711269859584), 40137898320880088898685190400, (-283262252382643103787159920448), 2736714339968684147836323840, 10397789891851353804938603520, 107358120145134595487316332160, (-269855654374109328942013074432), (-64958203116337253553186416640), 62048174840286250377471615360, (-407810053744394036799986855424), (-76234440996071599486567965696), 34334212708381455456078510720, (-61601252774566560248403809856), (-3643064774710323687151318080);
    0, 0, 0, 67857153248012696690557417920, (-257525599731044090332095603072), (-250035613153992555130917164160), 0, 26938054768915956547080299520, 194033469784353259931226659520, (-427118665829140012318671665664), 144815398977584902564238469120, 13754118016170436640963875200, (-39131524438430262956488166400), (-146681126187879869963054827776), 108764719492187495523823758720, (-200600888548931202482980410240), 15665890227639173647573109760, (-4825934151720440457534111360), 81230080233827884001777354880, (-179930434041311028671865720384), (-104705314036080079127219089920), 79809175822193160658596227520, (-291827342374605875527854962688), (-76051470685499854759204777728), 35835275630226305982805588800, (-62379702895308425464666569984), (-19131388094514114858764545920);
    0, 0, 0, 1038790532586077271397266831360, 933246016288125680449136362752, 589781433310776803550238525440, 0, (-31248680068389806346170327040), (-175898940359376302495129203200), 660423460256981518391401881600, (-913104996753270611892457324800), (-61741575853261449190957013760), 108578874393182342902077089280, 174542379725555727567048183168, (-215611931013658831074739322880), 354810123282508460480814859008, (-18172744553706045420866273280), (-8483509413437472405053153280), (-61844966550596661537206580480), 350779546058693552443928020608, 143769215263156783017346725120, (-130897110797427721185182096640), 568716995283441579725696004096, 117297515325384125345155051008, (-118603720443712608541093259520), 99896444739868416260606606592, 27208647767842035201500290560]

private def f408desc3IntegerForm : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2126429702386023246783353250048000, (-934798236445716458582065308186240), (-771433682651922302891203184737920), 866495074066757333377232256000000;
    (-934798236445716458582065308186240), 897610326664467791227910323553280, 565165215105658738534262523692160, (-1152860560320066083438040198230400);
    (-771433682651922302891203184737920), 565165215105658738534262523692160, 410341526923253690378873679525504, (-705753276671313909957942432130176);
    866495074066757333377232256000000, (-1152860560320066083438040198230400), (-705753276671313909957942432130176), 1643674129426275868931669354870784]

theorem f408desc3_compression_check :
    f408desc3ᵀ*f411rawM4Form*f408desc3=f408desc3Form := by
  have hD : natFourIntegerMatrix 210 f408desc3IntegerCoordinates=f408desc3 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 210 f408desc3IntegerCoordinates) (f408desc3) (by decide +kernel) a b
  have hV : f408desc3IntegerCoordinatesᵀ*f411rawInteger=f408desc3IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f408desc3IntegerCoordinatesᵀ*f411rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f408desc3IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f408desc3IntegerCoordinatesᵀ*f411rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f408desc3IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f408desc3IntegerCoordinatesᵀ*f411rawInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f408desc3IntegerLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f408desc3IntegerCoordinatesᵀ*f411rawInteger) 3 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f408desc3IntegerLeftProduct) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f408desc3IntegerLeftProduct*f408desc3IntegerCoordinates=f408desc3IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc3IntegerLeftProduct*f408desc3IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc3IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc3IntegerLeftProduct*f408desc3IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc3IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc3IntegerLeftProduct*f408desc3IntegerCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc3IntegerForm) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc3IntegerLeftProduct*f408desc3IntegerCoordinates) 3 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc3IntegerForm) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (210*1000000000000000000000000*210) f408desc3IntegerForm=f408desc3Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (210*1000000000000000000000000*210) f408desc3IntegerForm) (f408desc3Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 210
    f411rawInteger f408desc3IntegerCoordinates f408desc3IntegerLeftProduct f408desc3IntegerForm
    f411rawM4Form f408desc3 f408desc3Form f411_raw_integer_check hD hV hY hF

theorem f408desc3_source_form (x y : Fin 4 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3] (natFourWordBlock f408basis (complexify b408relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
          (natFourWordBlock f408basis (complexify b408relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f408desc3Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 3
    f408basis b408relative
    f411basis f408desc3 f411rawM4Form f408desc3Form
    f408desc3_actual f411_actual_raw_M4_matrix f408desc3_compression_check x y


#print axioms f408desc3_compression_check
#print axioms f408desc3_source_form
end TorusLean.BosonFiniteCertificate
