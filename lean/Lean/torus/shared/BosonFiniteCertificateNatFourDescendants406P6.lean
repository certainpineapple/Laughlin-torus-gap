import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates406
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger412
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

def f406desc6Form : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(646431520675134862701169263/97656250000000000000), (50690352491657963416598373/122070312500000000000), (-962496997039028742285501/3125000000000000000);
    (50690352491657963416598373/122070312500000000000), (4094687500303150993354118451/488281250000000000000), (7813108991900013117334427037/1953125000000000000000);
    (-962496997039028742285501/3125000000000000000), (7813108991900013117334427037/1953125000000000000000), (468992750315203523717588363/97656250000000000000)]

private def f406desc6IntegerCoordinates : Matrix (Fin 34) (Fin 3) ℤ :=
  !![(-3), 3, 3;
    (-36), 36, 36;
    (-72), 42, 32;
    (-120), 0, (-60);
    (-135), 15, (-145);
    (-36), 156, (-104);
    24, 126, (-24);
    (-54), 84, 94;
    0, (-60), (-20);
    (-180), (-420), (-440);
    (-180), (-180), (-240);
    540, 420, 440;
    0, (-270), (-120);
    (-1080), (-360), 240;
    (-720), 360, 1200;
    216, 324, 804;
    (-960), 360, 600;
    540, 1020, 400;
    450, 150, (-250);
    180, 0, 20;
    1350, (-360), (-330);
    720, (-480), (-400);
    720, (-780), (-20);
    756, (-576), 84;
    1080, 360, 0;
    (-2520), 1800, 960;
    540, (-2700), (-1560);
    (-720), (-480), (-1840);
    2700, (-3300), (-5000);
    (-1080), 1560, 840;
    (-4320), 3600, 2400;
    0, (-450), 0;
    1800, 0, 1800;
    600, 0, 600]

private def f406desc6IntegerLeftProduct : Matrix (Fin 3) (Fin 34) ℤ :=
  !![0, 0, 0, 0, 3354789677820969981233585664000, 2696192606752919721112037299200, 13357961799694327966566045542400, 0, 0, 31451040725734251989337600000, (-320375816566954900361474342400), 3334282576264806166128178195200, 49912032785546923152634368000, 139415703528135449127547699200, 591525344204686332291736558080, 548394028667165926529106854400, (-441081974569809428168987289600), 234979697232120008156878160640, 737739481630784154340757529600, 0, 2234114016783542395491225600, 451869103244004731555410828800, 510941143332740406868362616320, (-186135222721885691697771379200), (-100061455382553736590238540800), (-577324881047296324921092480000), 48477245442698532325164595200, (-417647522990329581783308947200), (-16738393961203017202464675840), (-745594098718249588588415308800), (-275669988971175553999027737600), 286051909941522178469607168000, (-150041042439385442977458938880), 0;
    0, 0, 0, 0, 2242954484404922204113831833600, 13901976461985813019421134617600, 14412037220251773809601486182400, 0, 0, 26517124183263653390956646400, 2746941131931503073239240179200, 4751916871141593043818941548800, 42082028071125011368164864000, (-56796036968572543147274496000), 1354620138121874547268869035520, 1584035806871264981180849856000, (-61413338121090723196869888000), 162989673107147326732330056960, (-429625625767590896633053209600), 0, 1883636959055090390149017600, 258932407006619919116441049600, 1022287801757612302854575239680, 535379609769446828914418188800, (-153815193420185740899886617600), (-4055375267664437983524940800), (-111042928863295023566437401600), 25116517434504355358343264000, 23512802683055386367812515840, 460347989712631190197607808000, 334548721775630065828716518400, (-244186744363476780011025254400), 92008278842978586692002913280, 0;
    0, 0, 0, 0, (-2565589149159671746145337753600), (-2311447647385163073636483840000), 5345612921589539047103433369600, 0, 0, 68647580313809624117899776000, 377819966370361152800585664000, 2657351643973631678232140832000, 108942031331026251018451660800, 218466631508222421766310400000, 946822406684827463200512299520, 998066016796846694536133107200, 345254257419115025402394624000, 270214005787432286949739848960, 207767616231921494428920729600, 0, 4876361803705910994608025600, 260452621019117205947167603200, 441533102065268051490812167680, 109994950934780427613832716800, 75404606974000234797692851200, 138173852812553049559440614400, (-59673715002460030261189708800), 179829449149519229806037088000, 77948319242224386207946506240, 422772147601188774861149568000, 313953282154396860316330982400, 65217487963474178817874329600, 22303052389278931963343431680, 0]

private def f406desc6IntegerForm : Matrix (Fin 3) (Fin 3) ℤ :=
  !![5957512894542042894653975927808000, 373729830850495832677896484454400, (-277199135147240277778224288000000);
    373729830850495832677896484454400, 7547328000558767910950311128883200, 3600280623467526044467703978649600;
    (-277199135147240277778224288000000), 3600280623467526044467703978649600, 4322237186904915674581294353408000]

theorem f406desc6_compression_check :
    f406desc6ᵀ*f412rawM4Form*f406desc6=f406desc6Form := by
  have hD : natFourIntegerMatrix 30 f406desc6IntegerCoordinates=f406desc6 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 30 f406desc6IntegerCoordinates) (f406desc6) (by decide +kernel) a b
  have hV : f406desc6IntegerCoordinatesᵀ*f412rawInteger=f406desc6IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f406desc6IntegerCoordinatesᵀ*f412rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f406desc6IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f406desc6IntegerCoordinatesᵀ*f412rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f406desc6IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f406desc6IntegerCoordinatesᵀ*f412rawInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f406desc6IntegerLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f406desc6IntegerLeftProduct*f406desc6IntegerCoordinates=f406desc6IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc6IntegerLeftProduct*f406desc6IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc6IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc6IntegerLeftProduct*f406desc6IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc6IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc6IntegerLeftProduct*f406desc6IntegerCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc6IntegerForm) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (30*1000000000000000000000000*30) f406desc6IntegerForm=f406desc6Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (30*1000000000000000000000000*30) f406desc6IntegerForm) (f406desc6Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 30
    f412rawInteger f406desc6IntegerCoordinates f406desc6IntegerLeftProduct f406desc6IntegerForm
    f412rawM4Form f406desc6 f406desc6Form f412_raw_integer_check hD hV hY hF

theorem f406desc6_source_form (x y : Fin 3 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6] (natFourWordBlock f406basis (complexify b406relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6]
          (natFourWordBlock f406basis (complexify b406relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f406desc6Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 6
    f406basis b406relative
    f412basis f406desc6 f412rawM4Form f406desc6Form
    f406desc6_actual f412_actual_raw_M4_matrix f406desc6_compression_check x y


#print axioms f406desc6_compression_check
#print axioms f406desc6_source_form
end TorusLean.BosonFiniteCertificate
