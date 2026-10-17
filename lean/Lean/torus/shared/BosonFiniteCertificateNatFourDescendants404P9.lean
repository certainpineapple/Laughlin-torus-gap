import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates404
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger413
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
import torus.shared.BosonFiniteCertificate404

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

def f404desc9Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(170010710805447258846920018703/7812500000000000000), (43493259057053746790864559969/1562500000000000000);
    (43493259057053746790864559969/1562500000000000000), (2086852688258837371205044613067/39062500000000000000)]

private def f404desc9IntegerCoordinates : Matrix (Fin 39) (Fin 2) ℤ :=
  !![1, (-1);
    23, (-23);
    78, (-72);
    158, (-104);
    225, (-9);
    261, 243;
    276, 480;
    144, (-150);
    756, (-768);
    1120, (-796);
    1170, 414;
    1152, 2376;
    588, 1680;
    690, (-792);
    1260, (-1440);
    1080, (-144);
    1512, 1008;
    480, (-1560);
    2520, (-7056);
    2016, (-4788);
    3150, (-8694);
    216, (-258);
    936, (-1374);
    144, (-270);
    (-864), 2916;
    (-1008), 5796;
    (-702), (-1080);
    (-8064), 3600;
    (-8568), 9072;
    (-3024), 5292;
    (-5376), 840;
    0, (-9576);
    1890, (-4410);
    (-2808), 1080;
    (-11592), 7560;
    (-3780), 6048;
    0, 2520;
    13860, (-5040);
    10080, (-2520)]

private def f404desc9IntegerLeftProduct : Matrix (Fin 2) (Fin 39) ℤ :=
  !![0, 0, 0, 0, 0, 70423771991907197221827998400000, 150336705191099545323683393932800, 0, 0, 0, 446365428888670889965845811200, 28616067003185340999236293824000, 40077392697958441962509178854400, 0, (-79337197891432847170409472000), 623251620928482612177519475200, 10187638257461580601925636332800, (-3143578091855377098148949721600), (-1280462335499167530635565619200), 1370596394119772063821524940800, (-413114712367000486912380806400), 0, 0, 226567619599638468596555980800, 1229028435945134154231811660800, 7341623562238772404473552326400, 14868152973811819118887833600, (-1821613064955205205542665945600), (-2356485495094257889510509696000), 648561584759609437192455091200, (-3252626401916110167367870348800), (-567773209372945481395049491200), 0, (-1105424853071684854990674355200), (-1541021310302245454303537472000), (-870404170039173669196777363200), (-664045262365037350364911123200), 0, 0;
    0, 0, 0, 0, 0, 65971089057952121813724609907200, 321329580992910944696641505702400, 0, 0, 0, 706782651738001447152254054400, 39316401962745270579794033856000, 82960605107549072372907676800000, 0, (-125623875528561953791813017600), 3317009645045738659365267494400, 18931527262273998050107954502400, (-4090228498142227414599217804800), (-2058212127110875924787671910400), (-553232010764221113394401638400), 2693470259196456648429271507200, 0, 0, 358751046474327829328545996800, 5523287842261533449526541747200, 12189171900275359213340788128000, 23542488933561489615787929600, (-1647415602446835809530992268800), (-3575238708130727505947413171200), (-676992441844700384680297958400), (-2285837711345392110239973696000), 725161891672373580587783520000, 0, (-1410880903967238994624040985600), 1808124832964500803628978291200, 1794647912801028286683308486400, (-111780239182815145515231340800), 0, 0]

private def f404desc9IntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![195852338847875242191651861545856000, 250521172168629581515379865421440000;
    250521172168629581515379865421440000, 480810859374836130325642278850636800]

theorem f404desc9_compression_check :
    f404desc9ᵀ*f413rawM4Form*f404desc9=f404desc9Form := by
  have hD : natFourIntegerMatrix 3 f404desc9IntegerCoordinates=f404desc9 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 3 f404desc9IntegerCoordinates) (f404desc9) (by decide +kernel) a b
  have hV : f404desc9IntegerCoordinatesᵀ*f413rawInteger=f404desc9IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f404desc9IntegerCoordinatesᵀ*f413rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f404desc9IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f404desc9IntegerCoordinatesᵀ*f413rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f404desc9IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f404desc9IntegerLeftProduct*f404desc9IntegerCoordinates=f404desc9IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc9IntegerLeftProduct*f404desc9IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc9IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc9IntegerLeftProduct*f404desc9IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc9IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc9IntegerForm=f404desc9Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc9IntegerForm) (f404desc9Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 3
    f413rawInteger f404desc9IntegerCoordinates f404desc9IntegerLeftProduct f404desc9IntegerForm
    f413rawM4Form f404desc9 f404desc9Form f413_raw_integer_check hD hV hY hF

theorem f404desc9_source_form (x y : Fin 2 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[9] (natFourWordBlock f404basis (complexify b404relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[9]
          (natFourWordBlock f404basis (complexify b404relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f404desc9Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 9
    f404basis b404relative
    f413basis f404desc9 f413rawM4Form f404desc9Form
    f404desc9_actual f413_actual_raw_M4_matrix f404desc9_compression_check x y


#print axioms f404desc9_compression_check
#print axioms f404desc9_source_form
end TorusLean.BosonFiniteCertificate
