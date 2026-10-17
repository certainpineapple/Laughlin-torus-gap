import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates407
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger412
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

def f407desc5Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(290099971610008787649378987/976562500000000000000), (-190148764483797576359868201/488281250000000000000);
    (-190148764483797576359868201/488281250000000000000), (154943289911940636596210971/244140625000000000000)]

private def f407desc5IntegerCoordinates : Matrix (Fin 34) (Fin 2) ℤ :=
  !![3, (-4);
    24, (-32);
    12, 4;
    0, 80;
    15, 60;
    (-24), (-48);
    (-36), (-52);
    6, (-28);
    (-180), 200;
    0, 160;
    240, (-160);
    (-120), (-80);
    (-180), 20;
    0, (-640);
    (-240), 80;
    (-396), 568;
    0, (-320);
    0, 960;
    150, 200;
    (-60), 40;
    (-90), 100;
    720, (-480);
    660, (-200);
    36, 232;
    360, (-400);
    720, (-800);
    (-1080), 1200;
    240, (-1440);
    1200, (-3200);
    (-360), 640;
    (-2520), 3440;
    (-900), 1100;
    1200, (-800);
    600, (-400)]

private def f407desc5IntegerLeftProduct : Matrix (Fin 2) (Fin 34) ℤ :=
  !![0, 0, 0, 0, (-3571159266156975466967783239680), (-2636835990885605412363522355200), (-5033696379849300359272890931200), 0, 0, (-30219352387358349547416268800), (-463754575081103752744494727680), (-1759074520389842844473563411200), (-47957373465975170532802252800), (-64320309114631157056618598400), (-911613106477391721969201016320), (-883531319382137241328350528000), (-51357362423336349194843136000), (-396296932854910092766484693760), (-274129899224826259061306449920), 0, (-2146622965284668871884083200), (-230871691483495516280601331200), (-632093315497326278073922613760), (-590776109274408544343351692800), 120491334566671177859097600, (-52157694576186617337266457600), (-387803466453826220927112668160), (-18952527364881347967695827200), (-96690394404214093348897812480), (-311606872544390239267616793600), (-136972394343458156819745561600), (-178160828082045609165755904000), (-26184706493984097102480384000), 0;
    0, 0, 0, 0, 2875770912153099508885107671040, (-1970877438015559919852268441600), 1422884450659509859833227059200, 0, 0, 18928867861489711703935795200, (-432009540149875111984780892160), 486934332890665941779583052800, 30039650444599337121631027200, 16140348141092774188105420800, 751284591046435633130852751360, 584866314150651444850248038400, 316825406743585428349361971200, 544050357614368733286284129280, 526938888094446437828858511360, 0, 1344607057052933473246003200, (-70430640843670529580784281600), 245615355210576249734221486080, 981521112928472798487855667200, 57536314690507679141782732800, 214828862499638214003759513600, 681256426729828680561655572480, 212900736374220153351369600000, 143099987648543325954889482240, 568412102679250671431114342400, 102881795982008736972480307200, 341074110710664122873151283200, 17543143029360891635610624000, 0]

private def f407desc5IntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1069424535343136394790670697676800, (-1401928810786142770986036272332800);
    (-1401928810786142770986036272332800), 2284731775725511850993088493977600]

theorem f407desc5_compression_check :
    f407desc5ᵀ*f412rawM4Form*f407desc5=f407desc5Form := by
  have hD : natFourIntegerMatrix 60 f407desc5IntegerCoordinates=f407desc5 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 60 f407desc5IntegerCoordinates) (f407desc5) (by decide +kernel) a b
  have hV : f407desc5IntegerCoordinatesᵀ*f412rawInteger=f407desc5IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f407desc5IntegerCoordinatesᵀ*f412rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f407desc5IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f407desc5IntegerCoordinatesᵀ*f412rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f407desc5IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f407desc5IntegerLeftProduct*f407desc5IntegerCoordinates=f407desc5IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc5IntegerLeftProduct*f407desc5IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc5IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc5IntegerLeftProduct*f407desc5IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc5IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (60*1000000000000000000000000*60) f407desc5IntegerForm=f407desc5Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (60*1000000000000000000000000*60) f407desc5IntegerForm) (f407desc5Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 60
    f412rawInteger f407desc5IntegerCoordinates f407desc5IntegerLeftProduct f407desc5IntegerForm
    f412rawM4Form f407desc5 f407desc5Form f412_raw_integer_check hD hV hY hF

theorem f407desc5_source_form (x y : Fin 2 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5] (natFourWordBlock f407basis (complexify b407relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
          (natFourWordBlock f407basis (complexify b407relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f407desc5Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 5
    f407basis b407relative
    f412basis f407desc5 f412rawM4Form f407desc5Form
    f407desc5_actual f412_actual_raw_M4_matrix f407desc5_compression_check x y


#print axioms f407desc5_compression_check
#print axioms f407desc5_source_form
end TorusLean.BosonFiniteCertificate
