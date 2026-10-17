import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates409
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger412
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

def f409desc3Form : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(233272652058592931619867087/17089843750000000000000), (-3631448537496556537401079713/546875000000000000000000), (-1265665767995591368270512741/546875000000000000000000);
    (-3631448537496556537401079713/546875000000000000000000), (703363218179983761131485173/62500000000000000000000), (1686457249715587151110356819/437500000000000000000000);
    (-1265665767995591368270512741/546875000000000000000000), (1686457249715587151110356819/437500000000000000000000), (-175538307465394241543803773/437500000000000000000000)]

private def f409desc3IntegerCoordinates : Matrix (Fin 34) (Fin 3) ℤ :=
  !![(-4), 5, 5;
    0, 0, 0;
    (-8), (-18), (-46);
    (-32), 54, (-2);
    76, 45, 45;
    32, (-54), 2;
    (-56), (-42), (-14);
    80, (-72), (-44);
    (-64), (-18), 94;
    (-160), 18, 186;
    288, (-234), (-178);
    (-224), 378, (-14);
    24, 54, 138;
    320, (-36), (-372);
    224, (-504), (-168);
    0, (-378), 294;
    (-448), 756, (-28);
    (-224), 126, 182;
    280, (-210), (-210);
    0, 84, 28;
    (-336), 378, 126;
    (-256), (-576), (-352);
    0, 126, (-98);
    0, 756, 252;
    768, (-540), (-540);
    (-448), (-252), 756;
    672, (-1134), 42;
    (-1792), 2016, 1792;
    1120, (-630), (-910);
    672, 0, 0;
    (-1344), 1512, 504;
    840, (-1890), (-2310);
    0, 0, 0;
    0, 280, 840]

private def f409desc3IntegerLeftProduct : Matrix (Fin 3) (Fin 34) ℤ :=
  !![0, 0, 0, 0, 458087660105273495491267215360, 1863627297493995674173882368000, (-1630790755157781039424875356160), 0, 0, (-37815724982180341889021952000), (-15217901247282620660913162240), (-875425346181383078144351185920), (-60012631100905773657845022720), (-138664600181947711600272875520), (-142181973534329424451926005760), (-246211903814095624767590983680), (-199515653307165210930507939840), (-100037808540556358436923857920), 184654734218034735404024340480, 0, (-2686229619036277349447516160), (-300896535746899086798472058880), (-512239061894401107357585868800), 336219960366498095516563015680, (-49200323099830824129519144960), (-190272335610361416551859179520), 113096883328012825730228551680, (-56694903682551623659996369920), (-54292946496292216831764234240), 137343699207292133702467031040, (-149305092772625170291855134720), 78133693718843378542068940800, (-64160153329748534936456601600), 0;
    0, 0, 0, 0, 1227826734336744362298804510720, (-4271065480625722559087360463360), (-3668401960534340761303983882240), 0, 0, 22391681946544941193297612800, 193850062468297024258263191040, (-117399867880552875361636035840), 35535052022033376319351541760, (-7244188831140350663939420160), 103523106243068857417863029760, (-15451739081510857164137664000), 416934753558068692711971855360, 48556583671560103155003160320, 172010558863027854931345205760, 0, 1590587543853292117859389440, 85945678342117060173458250240, 224218026597938270617607869440, (-285631330947888435565903234560), (-51619067595386689209272939520), 336889634592647801280387594240, (-161943287033002729921814592000), 225879019382095033571093064960, 89411850103561772310697927680, 132852885856818179156093583360, 142058815465869098698353776640, 112825527224344189290236390400, 35371706564758471493214435840, 0;
    0, 0, 0, 0, 3175872916009483410559326167040, (-3666461529826785168419040299520), (-118943110399207250499765166080), 0, 0, 5642618194689988096656691200, 4560012573844669353387118080, (-224433175555650598169156916480), 8954697159452519225214750720, (-25523939133724115693742981120), 158232948591585576833331563520, (-195751743935302574106092121600), 359228516959813595063745899520, 59582149131749855855894173440, 321627679679445434890944606720, 0, 400823071513937193496596480, 80699886892395857342190574080, 160779694828105144011059297280, (-337917906276042546603465131520), (-71337175529878626714158883840), 299320328991178694126595962880, (-37245203970982216501067942400), 176871610758367417166116773120, 95351285626038641959403074560, 210040711061728306934975569920, 126135052772945870435991828480, 198985225180749401356587187200, 14966742790519416072497594880, 0]

private def f409desc3IntegerForm : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1070142956771836245664772658954240, (-520604462335506345201818787655680), (-181445844499847978555260706549760);
    (-520604462335506345201818787655680), 882298820884971629963335001011200, 302213139149033217478975941964800;
    (-181445844499847978555260706549760), 302213139149033217478975941964800, (-31456464697798648084649636121600)]

theorem f409desc3_compression_check :
    f409desc3ᵀ*f412rawM4Form*f409desc3=f409desc3Form := by
  have hD : natFourIntegerMatrix 280 f409desc3IntegerCoordinates=f409desc3 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 280 f409desc3IntegerCoordinates) (f409desc3) (by decide +kernel) a b
  have hV : f409desc3IntegerCoordinatesᵀ*f412rawInteger=f409desc3IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f409desc3IntegerCoordinatesᵀ*f412rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f409desc3IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f409desc3IntegerCoordinatesᵀ*f412rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f409desc3IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f409desc3IntegerCoordinatesᵀ*f412rawInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f409desc3IntegerLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f409desc3IntegerLeftProduct*f409desc3IntegerCoordinates=f409desc3IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc3IntegerLeftProduct*f409desc3IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc3IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc3IntegerLeftProduct*f409desc3IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc3IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc3IntegerLeftProduct*f409desc3IntegerCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc3IntegerForm) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (280*1000000000000000000000000*280) f409desc3IntegerForm=f409desc3Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (280*1000000000000000000000000*280) f409desc3IntegerForm) (f409desc3Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 280
    f412rawInteger f409desc3IntegerCoordinates f409desc3IntegerLeftProduct f409desc3IntegerForm
    f412rawM4Form f409desc3 f409desc3Form f412_raw_integer_check hD hV hY hF

theorem f409desc3_source_form (x y : Fin 3 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3] (natFourWordBlock f409basis (complexify b409relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
          (natFourWordBlock f409basis (complexify b409relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f409desc3Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 3
    f409basis b409relative
    f412basis f409desc3 f412rawM4Form f409desc3Form
    f409desc3_actual f412_actual_raw_M4_matrix f409desc3_compression_check x y


#print axioms f409desc3_compression_check
#print axioms f409desc3_source_form
end TorusLean.BosonFiniteCertificate
