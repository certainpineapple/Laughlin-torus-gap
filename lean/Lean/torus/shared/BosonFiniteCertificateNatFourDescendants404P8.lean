import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates404
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger412
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

def f404desc8Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(21014402229941928823880140449/12207031250000000000), (78803281701535446689563475253/48828125000000000000);
    (78803281701535446689563475253/48828125000000000000), (18771135529980017343800409981/4882812500000000000)]

private def f404desc8IntegerCoordinates : Matrix (Fin 34) (Fin 2) ℤ :=
  !![1, (-1);
    20, (-20);
    58, (-52);
    100, (-52);
    125, 43;
    136, 200;
    70, 140;
    104, (-110);
    432, (-444);
    488, (-248);
    432, 576;
    448, 1400;
    258, (-348);
    256, (-496);
    392, (-224);
    336, (-84);
    224, (-1064);
    1680, (-4704);
    490, (-1330);
    112, (-148);
    168, (-486);
    (-512), 464;
    (-784), 1876;
    (-336), 1260;
    (-1296), 240;
    (-4704), 2688;
    (-2688), 2856;
    (-896), (-784);
    1400, (-3080);
    (-1512), 840;
    (-2352), 2352;
    630, 420;
    5600, (-1400);
    1120, (-280)]

private def f404desc8IntegerLeftProduct : Matrix (Fin 2) (Fin 34) ℤ :=
  !![0, 0, 0, 0, 3336812656855396592473783296000, 21779847740847544467950131937280, 21703088930846947644990169405440, 0, 0, (-76426796846683703147180544000), 1343866217089159029352978321920, 5663822326838493843015571587840, (-121287458791951231394693836800), (-277298151400973266431161333760), 490261615211545646113134190080, 1422389121644534146672905423360, (-666608524495839780958015488000), (-265392496077371244700620192000), 59013221518020867193957201920, 0, (-5428957018361582640267325440), (-206102241450803994153381296640), 210836051496886275019936811520, 557597809285200562408869219840, (-254288857962866541779735608320), (-819523545276746189945997757440), (-539598957542269096914595584000), (-709378884984500132546795293440), (-137730341843410990402237870080), (-740163108057678978829870740480), (-526929706206397975821688857600), (-91950098540705922038189137920), (-110251309968065528477802178560), 0;
    0, 0, 0, 0, 9612522120447547792706597068800, 31850596028060737230690973440000, 45510493387088887649503912396800, 0, 0, (-66284452963194415487996129280), 4599580764636576975486418030080, 11119857691023448467455789164800, (-105191807162575590516856688640), (-301319649087270998094923120640), 2504184356298666962389333547520, 3610299808215133634978360686080, 73283388393235963589987328000, 643002524466482943706935548160, 1511298139158177802665768529920, 0, (-4708494351358866341165813760), 177051453261698957488795906560, 2051014223379804245690974686720, 2032454780107194597256947202560, (-484515141760806227724885765120), 146928820199098463961323258880, 323441357588459801192178293760, 98027969963047442364878979840, 216899734756521392889767239680, 465659741025803665885575674880, 533579810712091169493153254400, 700688035406366721616002416640, (-78781667731517859520046561280), 0]

private def f404desc8IntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![15493498476091585283270349950238720, 14525020883227013533820339758632960;
    14525020883227013533820339758632960, 34598957008859167968092915676979200]

theorem f404desc8_compression_check :
    f404desc8ᵀ*f412rawM4Form*f404desc8=f404desc8Form := by
  have hD : natFourIntegerMatrix 3 f404desc8IntegerCoordinates=f404desc8 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 3 f404desc8IntegerCoordinates) (f404desc8) (by decide +kernel) a b
  have hV : f404desc8IntegerCoordinatesᵀ*f412rawInteger=f404desc8IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f404desc8IntegerCoordinatesᵀ*f412rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f404desc8IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f404desc8IntegerCoordinatesᵀ*f412rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f404desc8IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f404desc8IntegerLeftProduct*f404desc8IntegerCoordinates=f404desc8IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc8IntegerLeftProduct*f404desc8IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc8IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc8IntegerLeftProduct*f404desc8IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc8IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc8IntegerForm=f404desc8Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc8IntegerForm) (f404desc8Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 3
    f412rawInteger f404desc8IntegerCoordinates f404desc8IntegerLeftProduct f404desc8IntegerForm
    f412rawM4Form f404desc8 f404desc8Form f412_raw_integer_check hD hV hY hF

theorem f404desc8_source_form (x y : Fin 2 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8] (natFourWordBlock f404basis (complexify b404relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8]
          (natFourWordBlock f404basis (complexify b404relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f404desc8Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 8
    f404basis b404relative
    f412basis f404desc8 f412rawM4Form f404desc8Form
    f404desc8_actual f412_actual_raw_M4_matrix f404desc8_compression_check x y


#print axioms f404desc8_compression_check
#print axioms f404desc8_source_form
end TorusLean.BosonFiniteCertificate
