import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates409
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger411
import torus.shared.BosonFiniteCertificateNatFourRaise409
import torus.shared.BosonFiniteCertificateNatFourRaise410
import torus.shared.BosonFiniteCertificateNatFourRaise411
import torus.shared.BosonFiniteCertificateNatFourRaise412
import torus.shared.BosonFiniteCertificateNatFourRaise413
import torus.shared.BosonFiniteCertificateNatFourRaise414
import torus.shared.BosonFiniteCertificateNatFourRaise415
import torus.shared.BosonFiniteCertificate409

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

def f409desc2Form : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(2222071312954897614055119489/195312500000000000000000), (-1539084934173617442602028819/125000000000000000000000), (-46034604799002353114710531029/4375000000000000000000000);
    (-1539084934173617442602028819/125000000000000000000000), (91367156456407019300435523351/6250000000000000000000000), (548220680759652217816116350799/43750000000000000000000000);
    (-46034604799002353114710531029/4375000000000000000000000), (548220680759652217816116350799/43750000000000000000000000), (463381667689905454960136153493/43750000000000000000000000)]

private def f409desc2IntegerCoordinates : Matrix (Fin 27) (Fin 3) ℤ :=
  !![(-4), 5, 5;
    12, (-15), (-15);
    (-20), (-3), (-31);
    (-12), 57, 29;
    88, (-12), 16;
    (-56), (-42), (-14);
    56, (-42), (-14);
    (-136), 72, 184;
    0, (-168), (-56);
    112, (-42), (-154);
    (-112), 252, 84;
    160, (-18), (-46);
    0, 168, (-224);
    112, (-630), 210;
    (-448), 588, 196;
    280, (-210), (-210);
    (-56), 126, 42;
    (-32), (-72), (-184);
    (-224), (-336), (-112);
    112, 504, 168;
    672, (-378), (-126);
    (-1344), 1008, 1456;
    840, (-1260), (-980);
    0, 420, 140;
    0, 378, 126;
    0, (-630), (-1330);
    0, 280, 840]

private def f409desc2IntegerLeftProduct : Matrix (Fin 3) (Fin 27) ℤ :=
  !![0, 0, 0, (-104392456806079305909235491840), 462265932282664540949497668096, (-504581264994937207291369251840), 0, 4527549846955375436172533760, 70697434049392493954066641920, 217800745313588640805663208448, (-868915254729669452866199001600), (-139527693282242893220599104000), (-9480865462978099089587143680), (-144802396043032172513158027008), (-270046686022537789565393241600), 204240842930942656042711661568, 2633007410421214891138744320, (-34313748063347349567138954240), (-142608605310121510108068917760), (-81069334562874246558483195648), 7394533933233518464406330880, (-192448390605820664054209021440), 325727529175082758653094219776, 35320409061443954600306439168, (-98556450007900766051706693120), 14580764434244749727607293952, 11199623809158621311225264640;
    0, 0, 0, 521382249738221625334790455680, (-247816395084843591351570191232), (-50544532799319890534646435840), 0, 4751698247358425034712104960, (-41749544451633702041224056960), (-207811573644653943735592588032), 914324908330281997923937211520, 25332278905825507880598015360, 336561995612718262638800640, 169113464052096610630312721856, 359577256903430633559732297600, (-168773648626956408581359915776), 2763361494065075913681315840, 10506307702590643670810334720, 86118837341308467419282405760, 75384210069681811557587728704, (-19644720730440739634391615360), 258759843262010678928196846080, (-304866949919024621786225531904), (-42484695046043530221953397504), 182136583603225321908050016000, (-29182596276810175513068070656), (-19854797903092707171151248000);
    0, 0, 0, 1097023898415548989298983167360, (-264559536914132343503518141824), 49087155871453745792098321920, 0, (-8661705112959043344168775680), (-38558435048008333256597742720), (-238991772890554993533307233024), 725785821269558278439354663040, (-35222981147676009660598577280), 45604505834198959821835495680, 109838250980837342072488700352, 311770764004857318402265238400, (-121737552275893079304136760832), (-5037235344957693297034782720), 1408424251659376936409994240, 79926329843520448851681448320, 35197406720971793489152139328, 2334522836194252411169278080, 232012367684765973702507720960, (-223565246729501913520344142848), (-49422453261554600293637392128), 181190217592983734965956787200, (-41627341444417726174037563392), (-24248044591671615449210582400)]

private def f409desc2IntegerForm : Matrix (Fin 3) (Fin 3) ℤ :=
  !![891957201590599541462637403840512, (-965314070713692859999992475276800), (-824940117998122167815612716039680);
    (-965314070713692859999992475276800), 1146109610589169650104663204914944, 982411459921296774326480500631808;
    (-824940117998122167815612716039680), 982411459921296774326480500631808, 830379948500310575288563987059456]

theorem f409desc2_compression_check :
    f409desc2ᵀ*f411rawM4Form*f409desc2=f409desc2Form := by
  have hD : natFourIntegerMatrix 280 f409desc2IntegerCoordinates=f409desc2 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 280 f409desc2IntegerCoordinates) (f409desc2) (by decide +kernel) a b
  have hV : f409desc2IntegerCoordinatesᵀ*f411rawInteger=f409desc2IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f409desc2IntegerCoordinatesᵀ*f411rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f409desc2IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f409desc2IntegerCoordinatesᵀ*f411rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f409desc2IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f409desc2IntegerCoordinatesᵀ*f411rawInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f409desc2IntegerLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f409desc2IntegerLeftProduct*f409desc2IntegerCoordinates=f409desc2IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc2IntegerLeftProduct*f409desc2IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc2IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc2IntegerLeftProduct*f409desc2IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc2IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc2IntegerLeftProduct*f409desc2IntegerCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc2IntegerForm) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (280*1000000000000000000000000*280) f409desc2IntegerForm=f409desc2Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (280*1000000000000000000000000*280) f409desc2IntegerForm) (f409desc2Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 280
    f411rawInteger f409desc2IntegerCoordinates f409desc2IntegerLeftProduct f409desc2IntegerForm
    f411rawM4Form f409desc2 f409desc2Form f411_raw_integer_check hD hV hY hF

theorem f409desc2_source_form (x y : Fin 3 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2] (natFourWordBlock f409basis (complexify b409relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
          (natFourWordBlock f409basis (complexify b409relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f409desc2Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 2
    f409basis b409relative
    f411basis f409desc2 f411rawM4Form f409desc2Form
    f409desc2_actual f411_actual_raw_M4_matrix f409desc2_compression_check x y


#print axioms f409desc2_compression_check
#print axioms f409desc2_source_form
end TorusLean.BosonFiniteCertificate
