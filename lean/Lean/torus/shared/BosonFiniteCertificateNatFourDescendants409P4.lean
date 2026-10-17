import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates409
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger413
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

def f409desc4Form : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(4549277105833193447719480911/38281250000000000000000), (-69545999252284987858932936537/1531250000000000000000000), (-33986521547548679014424843949/1531250000000000000000000);
    (-69545999252284987858932936537/1531250000000000000000000), (263884267979721826659300083283/3062500000000000000000000), (134737401676158114498406300221/3062500000000000000000000);
    (-33986521547548679014424843949/1531250000000000000000000), (134737401676158114498406300221/3062500000000000000000000), (114245349140384131510213623927/3062500000000000000000000)]

private def f409desc4IntegerCoordinates : Matrix (Fin 39) (Fin 3) ℤ :=
  !![(-4), 5, 5;
    (-12), 15, 15;
    (-8), (-18), (-46);
    (-40), 36, (-48);
    44, 99, 43;
    108, (-9), 47;
    (-80), (-138), (-26);
    80, (-72), (-44);
    80, (-198), (-86);
    (-288), 108, 276;
    280, (-126), 98;
    128, 36, (-188);
    (-336), 294, (-42);
    (-40), 36, 232;
    208, 90, 90;
    832, (-774), (-718);
    0, (-882), 406;
    (-128), 720, (-400);
    (-896), 1134, (-42);
    (-224), (-252), 476;
    616, (-504), (-448);
    80, 12, (-16);
    (-400), 612, 304;
    (-752), (-180), (-40);
    32, (-684), (-628);
    (-224), 2016, 392;
    120, 270, (-150);
    896, (-2520), (-1400);
    448, (-1638), 434;
    672, 0, 840;
    (-2688), 2520, 2520;
    (-896), 1764, 1988;
    1400, (-840), (-1120);
    1440, (-540), (-540);
    224, 1260, 1260;
    1008, (-3402), (-4074);
    (-4480), 5040, 2800;
    2800, (-4410), (-5530);
    0, 1120, 3360]

private def f409desc4IntegerLeftProduct : Matrix (Fin 3) (Fin 39) ℤ :=
  !![0, 0, 0, 0, 0, 11738170558470587465645115033600, (-22305862053552171587350869964800), 0, 0, 0, 56026212270862196698571980800, (-2627939810606381706770278963200), (-7821094614873629858158413312000), 0, (-9958125597569983284808089600), 284771405991406828655279462400, (-440127244327202008261070976000), (-667437386450567036443043788800), (-383827816226870866187349811200), (-434728956176025526210832179200), 605952856993465921702549017600, 0, 0, 28437966385747033204931788800, (-758898137486893554679386009600), (-581646370847231429114998348800), 1866197039427376488703180800, (-377694032871774899574027417600), (-376220021398762468824788889600), 43217745602539765309149081600, 42864408611083060525061683200, (-22685875922750759236903449600), 0, 955718864185317620629654425600, (-144735396627912464109241497600), 553014201553665229373878656000, (-314597882251834097325564441600), 0, 0;
    0, 0, 0, 0, 0, (-16984125067745878518014328499200), (-9950101366680399488273425958400), 0, 0, 0, (-13813402833188859807967334400), 296385797857518693931993804800, (-3650596249761536754239992857600), 0, 2455201289074377568564224000, 426647494916601410403806400000, (-1400334834628257064944004972800), 217574925676094813102542425600, (-849856117816059523414356556800), 429529075830020848572103449600, (-460999681334433597550872096000), 0, 0, (-7011450273755565245325312000), 217618871374497305988906624000, (-739414693876328565916613817600), (-460113683403571803796377600), 130398600100713223193362828800, (-1324647657232482897747393868800), 65208695902311026503365580800, 1090964678867787954291151449600, 56533449872963523751879968000, 0, 252250898067435737699083008000, 250521793077519906662510784000, (-420895534468975213014276768000), 278797786702276819322844230400, 0, 0;
    0, 0, 0, 0, 0, (-5527829219539592436109779686400), (-1693865726410529483074969228800), 0, 0, 0, (-54346008511708635333033676800), (-1184407614865213779212530790400), (-3594975285597769806200762803200), 0, 9659486271791790381782016000, (-132996031235667925089129792000), (-1214341809527714776768108857600), 103180871173190552586007027200, (-1210452539573056425813683481600), 434221572687631423373482675200, (-253954913875324973257471776000), 0, 0, (-27585122965883155016773632000), (-43469388280158184232445312000), (-840344670119669417272362067200), (-1810229562659760243698995200), 154637752935240668600873049600, (-1463739061378018222295900697600), 293196313068932795092110489600, 769384682235148692957321715200, 60654722869027999898987040000, 0, 116567991741781043759054592000, 330944856920242649298889920000, (-198701742838422426561231264000), 186420523715279860735913644800, 0, 0]

private def f409desc4IntegerForm : Matrix (Fin 3) (Fin 3) ℤ :=
  !![9316919512746380180929496905728000, (-3560755161716991378377366350694400), (-1740109903234492365538552010188800);
    (-3560755161716991378377366350694400), 6755437260280878762478082132044800, 3449277482909647731159201285657600;
    (-1740109903234492365538552010188800), 3449277482909647731159201285657600, 2924680937993833766661468772531200]

theorem f409desc4_compression_check :
    f409desc4ᵀ*f413rawM4Form*f409desc4=f409desc4Form := by
  have hD : natFourIntegerMatrix 280 f409desc4IntegerCoordinates=f409desc4 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 280 f409desc4IntegerCoordinates) (f409desc4) (by decide +kernel) a b
  have hV : f409desc4IntegerCoordinatesᵀ*f413rawInteger=f409desc4IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f409desc4IntegerCoordinatesᵀ*f413rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f409desc4IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f409desc4IntegerCoordinatesᵀ*f413rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f409desc4IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f409desc4IntegerCoordinatesᵀ*f413rawInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f409desc4IntegerLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f409desc4IntegerLeftProduct*f409desc4IntegerCoordinates=f409desc4IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc4IntegerLeftProduct*f409desc4IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc4IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc4IntegerLeftProduct*f409desc4IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc4IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc4IntegerLeftProduct*f409desc4IntegerCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc4IntegerForm) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (280*1000000000000000000000000*280) f409desc4IntegerForm=f409desc4Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (280*1000000000000000000000000*280) f409desc4IntegerForm) (f409desc4Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 280
    f413rawInteger f409desc4IntegerCoordinates f409desc4IntegerLeftProduct f409desc4IntegerForm
    f413rawM4Form f409desc4 f409desc4Form f413_raw_integer_check hD hV hY hF

theorem f409desc4_source_form (x y : Fin 3 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4] (natFourWordBlock f409basis (complexify b409relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
          (natFourWordBlock f409basis (complexify b409relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f409desc4Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 4
    f409basis b409relative
    f413basis f409desc4 f413rawM4Form f409desc4Form
    f409desc4_actual f413_actual_raw_M4_matrix f409desc4_compression_check x y


#print axioms f409desc4_compression_check
#print axioms f409desc4_source_form
end TorusLean.BosonFiniteCertificate
