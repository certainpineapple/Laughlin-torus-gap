import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates407
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger413
import torus.shared.BosonFiniteCertificateNatFourRaise407
import torus.shared.BosonFiniteCertificateNatFourRaise408
import torus.shared.BosonFiniteCertificateNatFourRaise409
import torus.shared.BosonFiniteCertificateNatFourRaise410
import torus.shared.BosonFiniteCertificateNatFourRaise411
import torus.shared.BosonFiniteCertificateNatFourRaise412
import torus.shared.BosonFiniteCertificateNatFourRaise413
import torus.shared.BosonFiniteCertificateNatFourRaise414
import torus.shared.BosonFiniteCertificateNatFourRaise415
import torus.shared.BosonFiniteCertificate407

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

def f407desc6Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(41575399223980290560824568643/15625000000000000000000), (-1341308333733048251415204903/1953125000000000000000);
    (-1341308333733048251415204903/1953125000000000000000), (3244661182400456437878735227/976562500000000000000)]

private def f407desc6IntegerCoordinates : Matrix (Fin 39) (Fin 2) ℤ :=
  !![3, (-4);
    33, (-44);
    36, (-28);
    12, 84;
    15, 140;
    (-9), 12;
    (-96), (-152);
    54, (-92);
    (-144), 152;
    (-180), 520;
    270, 120;
    72, (-336);
    (-192), (-184);
    (-360), 220;
    (-360), (-440);
    0, (-720);
    (-1152), 1136;
    0, (-960);
    (-240), 400;
    (-396), 1528;
    450, 1560;
    (-54), 12;
    (-450), 420;
    630, (-220);
    1620, (-840);
    612, 184;
    0, (-180);
    2880, (-3200);
    720, 80;
    (-1404), 2232;
    960, (-2560);
    1800, (-7120);
    1350, (-3000);
    0, 240;
    (-2880), 4560;
    (-5400), 6840;
    (-3600), 4640;
    1800, (-2600);
    3600, (-2400)]

private def f407desc6IntegerLeftProduct : Matrix (Fin 2) (Fin 39) ℤ :=
  !![0, 0, 0, 0, 0, (-26137174101812644981505109696000), (-32003102618299386126304388236800), 0, 0, 0, 39317323642757346179943936000, (-6243742940697419431245570777600), (-9700830750839874748408015027200), 0, (-6988279505783651542010880000), (-106146575472107988824224780800), (-3028514335074265538175490310400), (-57996119587913088503989132800), (-474710754777004001197288396800), (-844654733537219340791702169600), (-345923156465064046945741996800), 0, 0, 19956814693126507646843904000, (-675058529289514848532419456000), (-1764585058303472069059664659200), 1309636662775430870826086400, (-149388736180757799656506867200), (-483427365332300949628577664000), (-871511657169984196267576396800), 778168507489535072099533248000, (-109462927071496157589258835200), 0, 328130601043804348899170073600, (-396629740017361666869511104000), (-220739028707072263905266515200), 29149662502878053189153760000, 0, 0;
    0, 0, 0, 0, 0, 16129342430998721389790330112000, (-20691048141743833841522516121600), 0, 0, 0, (-165856953720002480317089792000), (-3269221031747357674772002099200), (-5744875643574742608618745958400), 0, 29479493421144625274228736000, 671334781941392332659998054400, (-438789208552499967786279244800), 584114287854818914728156518400, (-120321556719178985190896025600), 424975875994153628224863436800, 968170258215647441204965862400, 0, 0, (-84186212989316288766676992000), (-242052673564308311218386432000), (-1074672842067711276944276966400), (-5524592770957885657262899200), 327088090056479935391053977600, (-139200381423649654400060928000), 934171177793429385723003494400, 202916171476050713342684928000, 213831075257987814118874649600, 0, 983449347763841599932335923200, 494847360104768373973038336000, 793502346339648672186424089600, (-215434487517648833648737152000), 0, 0]

private def f407desc6IntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![9578971981205058945213980615347200, (-2472299520736754537008505677209600);
    (-2472299520736754537008505677209600), 11961118982801042612596169540812800]

theorem f407desc6_compression_check :
    f407desc6ᵀ*f413rawM4Form*f407desc6=f407desc6Form := by
  have hD : natFourIntegerMatrix 60 f407desc6IntegerCoordinates=f407desc6 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 60 f407desc6IntegerCoordinates) (f407desc6) (by decide +kernel) a b
  have hV : f407desc6IntegerCoordinatesᵀ*f413rawInteger=f407desc6IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f407desc6IntegerCoordinatesᵀ*f413rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f407desc6IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f407desc6IntegerCoordinatesᵀ*f413rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f407desc6IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f407desc6IntegerLeftProduct*f407desc6IntegerCoordinates=f407desc6IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc6IntegerLeftProduct*f407desc6IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc6IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc6IntegerLeftProduct*f407desc6IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc6IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (60*1000000000000000000000000*60) f407desc6IntegerForm=f407desc6Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (60*1000000000000000000000000*60) f407desc6IntegerForm) (f407desc6Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 60
    f413rawInteger f407desc6IntegerCoordinates f407desc6IntegerLeftProduct f407desc6IntegerForm
    f413rawM4Form f407desc6 f407desc6Form f413_raw_integer_check hD hV hY hF

theorem f407desc6_source_form (x y : Fin 2 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6] (natFourWordBlock f407basis (complexify b407relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6]
          (natFourWordBlock f407basis (complexify b407relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f407desc6Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 6
    f407basis b407relative
    f413basis f407desc6 f413rawM4Form f407desc6Form
    f407desc6_actual f413_actual_raw_M4_matrix f407desc6_compression_check x y


#print axioms f407desc6_compression_check
#print axioms f407desc6_source_form
end TorusLean.BosonFiniteCertificate
