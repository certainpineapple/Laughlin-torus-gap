import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates409
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger409
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

def f409desc0Form : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(-610746523548250434721014171/1367187500000000000000000), (18696812056305257564351889561/43750000000000000000000000), (14583417297376722738248037027/43750000000000000000000000);
    (18696812056305257564351889561/43750000000000000000000000), (-89957784880618381648542961701/175000000000000000000000000), (-68035466759205132189629563977/175000000000000000000000000);
    (14583417297376722738248037027/43750000000000000000000000), (-68035466759205132189629563977/175000000000000000000000000), (-49015221333459777527133037629/175000000000000000000000000)]

private def f409desc0IntegerCoordinates : Matrix (Fin 18) (Fin 3) ℤ :=
  !![(-4), 5, 5;
    36, (-45), (-45);
    (-80), 72, 44;
    112, (-42), (-14);
    (-56), 0, 0;
    (-64), 108, 136;
    224, (-378), (-266);
    (-448), 252, 84;
    280, 0, 0;
    0, 378, 126;
    0, (-630), (-70);
    0, 280, 0;
    0, 0, (-140);
    0, 0, 420;
    0, 0, (-140);
    0, 0, (-420);
    0, 0, 280;
    0, 0, 0]

private def f409desc0IntegerLeftProduct : Matrix (Fin 3) (Fin 18) ℤ :=
  !![0, 15062399967037408416717672960, 124333927693787668261174796544, (-58335796954642958207363450880), 33045129478439696509140579840, 9443439630954719159133638400, (-22789261345271396885205441024), 20309960441159423431995662976, (-8664312016383054360744576768), 14434865155674546973955683200, 1030882278126003056549434368, 11503869442551854812039034880, (-2041983012157740223521500160), 18569670670954477953230774784, (-5465706301687457575990157568), (-3527195615524918636983338496), (-2167077712825572152421338880), 4893108044434604265280681728;
    0, 39981448585087742846647356480, (-140990209678585084795668411840), 59666988419608770485038164096, (-94314074878978758010803949056), (-11467361085266977993466199360), 7384392892377901656222598080, (-23907384801011213957589323328), (-15273843295973918318997152832), (-31963979327317520026206846240), (-2261866282833262116271840992), (-18331317577795779576694493280), 10867880274406092467976663360, (-20966189277561274682422113600), 4247226997720098253293348000, 2362691396187422975594188800, (-1165754504618259151582748160), (-5260740136578622695629740320);
    0, 73117304714554387603191207360, (-130623370258972651035489716160), 23545488001375676696714044992, (-34380255319547080061607445632), (-8192109275708840824542822720), (-5840918181070894386087892800), (-24443821662799050787346572416), (-5991997048610197807549591104), (-29297549437745855101260456480), (-5619196741879212331185343584), (-15802548974371412478009882720), 3557529752852582688885664320, (-20109867076066541724053363520), 1972721523390098173748479200, (-3630211100237451376906890240), 57451674758264596518737280, (-3766294687223516445732924000)]

private def f409desc0IntegerForm : Matrix (Fin 3) (Fin 3) ℤ :=
  !![(-35022648646350872928641836621824), 33504687204899021555318586093312, 26133483796899087146940482352384;
    33504687204899021555318586093312, (-40301087626517034978547246842048), (-30479889108123899220954044661696);
    26133483796899087146940482352384, (-30479889108123899220954044661696), (-21958819157389980332155600857792)]

theorem f409desc0_compression_check :
    f409desc0ᵀ*f409rawM4Form*f409desc0=f409desc0Form := by
  have hD : natFourIntegerMatrix 280 f409desc0IntegerCoordinates=f409desc0 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 280 f409desc0IntegerCoordinates) (f409desc0) (by decide +kernel) a b
  have hV : f409desc0IntegerCoordinatesᵀ*f409rawInteger=f409desc0IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 18) => (f409desc0IntegerCoordinatesᵀ*f409rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 18) => (f409desc0IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 18) => (f409desc0IntegerCoordinatesᵀ*f409rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 18) => (f409desc0IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 18) => (f409desc0IntegerCoordinatesᵀ*f409rawInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 18) => (f409desc0IntegerLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f409desc0IntegerLeftProduct*f409desc0IntegerCoordinates=f409desc0IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc0IntegerLeftProduct*f409desc0IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc0IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc0IntegerLeftProduct*f409desc0IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc0IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc0IntegerLeftProduct*f409desc0IntegerCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc0IntegerForm) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (280*1000000000000000000000000*280) f409desc0IntegerForm=f409desc0Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (280*1000000000000000000000000*280) f409desc0IntegerForm) (f409desc0Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 280
    f409rawInteger f409desc0IntegerCoordinates f409desc0IntegerLeftProduct f409desc0IntegerForm
    f409rawM4Form f409desc0 f409desc0Form f409_raw_integer_check hD hV hY hF

theorem f409desc0_source_form (x y : Fin 3 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0] (natFourWordBlock f409basis (complexify b409relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
          (natFourWordBlock f409basis (complexify b409relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f409desc0Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 0
    f409basis b409relative
    f409basis f409desc0 f409rawM4Form f409desc0Form
    f409desc0_actual f409_actual_raw_M4_matrix f409desc0_compression_check x y


#print axioms f409desc0_compression_check
#print axioms f409desc0_source_form
end TorusLean.BosonFiniteCertificate
