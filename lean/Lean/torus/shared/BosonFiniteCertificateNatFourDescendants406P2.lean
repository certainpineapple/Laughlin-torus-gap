import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates406
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger408
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

def f406desc2Form : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(-213930795193612783072114743/390625000000000000000000), (24120727448411498226474189/195312500000000000000000), (-8792166243058164610750837/390625000000000000000000);
    (24120727448411498226474189/195312500000000000000000), (9974373159971659881566487/390625000000000000000000), (-70689372661458146925798121/781250000000000000000000);
    (-8792166243058164610750837/390625000000000000000000), (-70689372661458146925798121/781250000000000000000000), (-53836643774093095973367299/1171875000000000000000000)]

private def f406desc2IntegerCoordinates : Matrix (Fin 15) (Fin 3) ℤ :=
  !![(-3), 3, 3;
    0, 0, 0;
    (-18), (-12), (-22);
    (-12), 12, (-8);
    15, 15, 5;
    54, (-24), (-14);
    (-72), 12, 52;
    60, (-60), 40;
    (-90), 60, 50;
    60, 0, (-60);
    36, 24, 4;
    (-90), 60, (-10);
    60, (-120), (-100);
    0, 0, 0;
    0, 30, 60]

private def f406desc2IntegerLeftProduct : Matrix (Fin 3) (Fin 15) ℤ :=
  !![(-16020527904798899475605771520), (-4467949424286684673268304000), 5807323079975597911071614208, 6261360168113169895321628832, (-4553463303930371547991295232), (-1045301595356834684592710400), (-343262826901294568692547328), 34217551782483859576408608, 1293404804282066315896656000, 1031986725408726340206415104, (-3930424028016102987272268480), (-492630856630428898387547136), (-1861067042441264151819277632), 1425124365873320205613652256, 870135458650621801920808704;
    6650180654188202092257793920, (-4388834457881877947475769920), 1700031926230713312224113152, 1307344920618103492098413088, 7850134671499400629195636992, (-516427973288070283374266880), (-1736818746008118246695120832), (-776032540064801892232751808), (-1909319267676264174104365440), (-2318560778674658435357882304), (-1397876108295938890752740160), (-985208079958593723717980544), (-1033943562120344122494430848), (-2353588812624735314191538496), (-2165877367169375411086719744);
    2666932216734102696048424320, (-6392983050533013252256141440), 6354694576555940942713582272, (-2273555972705105864222813472), 7431030187743805097800492032, (-111278890597022675974880640), (-381973243970218805258052672), 86535069114696224812963872, (-1198466861077141014293875200), (-2012873778087169307169570624), (-1705360203507760988623513920), (-936191869501222686593938944), (-1220983097424276584464298688), (-2261586901486622289391081056), (-2258870448435195251914689024)]

private def f406desc2IntegerForm : Matrix (Fin 3) (Fin 3) ℤ :=
  !![(-492896552126083852198152367872), 111148312082280183827593062912, (-20257151024006011263169928448);
    111148312082280183827593062912, 22980955760574704367129186048, (-81434157305999785258519435392);
    (-20257151024006011263169928448), (-81434157305999785258519435392), (-41346542418503497707546085632)]

theorem f406desc2_compression_check :
    f406desc2ᵀ*f408rawM4Form*f406desc2=f406desc2Form := by
  have hD : natFourIntegerMatrix 30 f406desc2IntegerCoordinates=f406desc2 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 30 f406desc2IntegerCoordinates) (f406desc2) (by decide +kernel) a b
  have hV : f406desc2IntegerCoordinatesᵀ*f408rawInteger=f406desc2IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 15) => (f406desc2IntegerCoordinatesᵀ*f408rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 15) => (f406desc2IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 15) => (f406desc2IntegerCoordinatesᵀ*f408rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 15) => (f406desc2IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 15) => (f406desc2IntegerCoordinatesᵀ*f408rawInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 15) => (f406desc2IntegerLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f406desc2IntegerLeftProduct*f406desc2IntegerCoordinates=f406desc2IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc2IntegerLeftProduct*f406desc2IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc2IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc2IntegerLeftProduct*f406desc2IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc2IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc2IntegerLeftProduct*f406desc2IntegerCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc2IntegerForm) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (30*1000000000000000000000000*30) f406desc2IntegerForm=f406desc2Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (30*1000000000000000000000000*30) f406desc2IntegerForm) (f406desc2Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 30
    f408rawInteger f406desc2IntegerCoordinates f406desc2IntegerLeftProduct f406desc2IntegerForm
    f408rawM4Form f406desc2 f406desc2Form f408_raw_integer_check hD hV hY hF

theorem f406desc2_source_form (x y : Fin 3 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2] (natFourWordBlock f406basis (complexify b406relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
          (natFourWordBlock f406basis (complexify b406relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f406desc2Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 2
    f406basis b406relative
    f408basis f406desc2 f408rawM4Form f406desc2Form
    f406desc2_actual f408_actual_raw_M4_matrix f406desc2_compression_check x y


#print axioms f406desc2_compression_check
#print axioms f406desc2_source_form
end TorusLean.BosonFiniteCertificate
