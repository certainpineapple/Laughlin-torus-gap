import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates409
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger410
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

def f409desc1Form : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(-321490566105915954631241991/273437500000000000000000), (22635032002796648945053639143/21875000000000000000000000), (14622517156341604316863631031/21875000000000000000000000);
    (22635032002796648945053639143/21875000000000000000000000), (-41808234146612673709445372037/43750000000000000000000000), (-31921564424547433256722734309/43750000000000000000000000);
    (14622517156341604316863631031/21875000000000000000000000), (-31921564424547433256722734309/43750000000000000000000000), (-31589465686575710157709796613/43750000000000000000000000)]

private def f409desc1IntegerCoordinates : Matrix (Fin 23) (Fin 3) ℤ :=
  !![(-4), 5, 5;
    24, (-30), (-30);
    (-44), 27, (-1);
    32, 30, 30;
    56, (-42), (-14);
    (-56), 0, 0;
    8, 18, 46;
    (-64), (-18), 94;
    0, (-210), (-210);
    0, 252, 84;
    224, 0, (-140);
    (-448), 378, 266;
    280, (-630), (-70);
    0, 210, (-70);
    (-64), 108, (-4);
    224, (-378), (-266);
    (-448), 252, 364;
    280, 0, (-140);
    0, 378, 546;
    0, (-630), (-630);
    0, 280, 280;
    0, 0, (-420);
    0, 0, 280]

private def f409desc1IntegerLeftProduct : Matrix (Fin 3) (Fin 23) ℤ :=
  !![0, 0, (-206618926830110812367166243840), 389848376648510067660427980288, (-156429151442615335940328218112), 181317391700000969875129052160, (-2767635005653930377547653120), 2938428956206622154711052800, 30681797770765840046849008128, (-47268098579909820052370519808), (-37285002463425931151521566720), 45133454362365552583197811968, (-112560744881184472958892678144), 14628548781467812457998774272, (-139503733283034083454059520), (-9151318709963696841417876480), 16686144956840791033990671360, (-89339829401039982773226614784), 178238494019577603502786560, 23146255637161630759866258432, 9695191506610096944813017088, (-29143274334194690055746270208), 10760782963544922751489471488;
    0, 0, 246399845819509218281526426240, (-277720577366382651380449804416), 103598065722332710061654583168, (-341311979971895347994052637440), 1348737917366241038652825600, (-50667020545685940308157719040), 7166530172883386847984379776, 16876705801480242250328806464, 1400336214181558995583054080, (-27256403776684277612790487872), 102384761051512070324237294208, 14876235953307420517696654080, (-7080092940228404082720007680), (-775096932092324502698496000), (-20894540827224457934263054080), 78041531386889783231843669760, 23236323468869226899684712960, (-7308846235277513029998387072), (-30514866780242934127203024384), 30472389071662284910329130368, (-15659484267686430405794128128);
    0, 0, 297296371133217068819321431680, (-193463138021891301253691551872), 10094926645911823985626793856, (-78528272390267189986195342080), 3707064952577468507425075200, (-61641214387376299187146414080), 15935011103558390155660847232, (-48947573458474950690720192), 6459097685358645721917346560, (-12662629190174246201656540224), 79044668644270136540782578816, 12322224195839922227046485760, (-11188608742629215648892610560), 673782409946802854313561600, (-28395382258967772963958364160), 71075129992727506289747377920, 24042699491022992902199992320, (-4307759161420158553934254464), (-28594754191747121572298216448), 28307180446819354160145357696, (-22314716424187795875396116736)]

private def f409desc1IntegerForm : Matrix (Fin 3) (Fin 3) ℤ :=
  !![(-92177775113888222511869703659520), 81123954698023189819072242688512, 52407101488328309871639253615104;
    81123954698023189819072242688512, (-74920355590729911287326106690304), (-57203443448789000396047139881728);
    52407101488328309871639253615104, (-57203443448789000396047139881728), (-56608322510343672602615955530496)]

theorem f409desc1_compression_check :
    f409desc1ᵀ*f410rawM4Form*f409desc1=f409desc1Form := by
  have hD : natFourIntegerMatrix 280 f409desc1IntegerCoordinates=f409desc1 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 280 f409desc1IntegerCoordinates) (f409desc1) (by decide +kernel) a b
  have hV : f409desc1IntegerCoordinatesᵀ*f410rawInteger=f409desc1IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f409desc1IntegerCoordinatesᵀ*f410rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f409desc1IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f409desc1IntegerCoordinatesᵀ*f410rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f409desc1IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f409desc1IntegerCoordinatesᵀ*f410rawInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f409desc1IntegerLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f409desc1IntegerLeftProduct*f409desc1IntegerCoordinates=f409desc1IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc1IntegerLeftProduct*f409desc1IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc1IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc1IntegerLeftProduct*f409desc1IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc1IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc1IntegerLeftProduct*f409desc1IntegerCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f409desc1IntegerForm) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (280*1000000000000000000000000*280) f409desc1IntegerForm=f409desc1Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (280*1000000000000000000000000*280) f409desc1IntegerForm) (f409desc1Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 280
    f410rawInteger f409desc1IntegerCoordinates f409desc1IntegerLeftProduct f409desc1IntegerForm
    f410rawM4Form f409desc1 f409desc1Form f410_raw_integer_check hD hV hY hF

theorem f409desc1_source_form (x y : Fin 3 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1] (natFourWordBlock f409basis (complexify b409relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
          (natFourWordBlock f409basis (complexify b409relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f409desc1Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 1
    f409basis b409relative
    f410basis f409desc1 f410rawM4Form f409desc1Form
    f409desc1_actual f410_actual_raw_M4_matrix f409desc1_compression_check x y


#print axioms f409desc1_compression_check
#print axioms f409desc1_source_form
end TorusLean.BosonFiniteCertificate
