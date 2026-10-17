import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates400
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger412
import torus.shared.BosonFiniteCertificateNatFourRaise400
import torus.shared.BosonFiniteCertificateNatFourRaise401
import torus.shared.BosonFiniteCertificateNatFourRaise402
import torus.shared.BosonFiniteCertificateNatFourRaise403
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
import torus.shared.BosonFiniteCertificate400

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

def f400desc12Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(759211779549850152012079066630233/76293945312500000)]

private def f400desc12IntegerCoordinates : Matrix (Fin 34) (Fin 1) ℤ :=
  !![4;
    144;
    792;
    2640;
    5940;
    9504;
    5544;
    1584;
    15840;
    47520;
    95040;
    133056;
    35640;
    190080;
    332640;
    199584;
    221760;
    665280;
    138600;
    5280;
    71280;
    190080;
    332640;
    199584;
    285120;
    1330560;
    1995840;
    1330560;
    1663200;
    332640;
    1995840;
    1247400;
    3326400;
    369600]

private def f400desc12IntegerLeftProduct : Matrix (Fin 1) (Fin 34) ℤ :=
  !![0, 0, 0, 0, 2924953625769490403681960843182080, 2294710670535887007348258023424000, 6521543206545671023909916998656000, 0, 0, (-8337105158807936080578742272000), 657918713504167363828223137105920, 2890670113150131641456665422720000, (-13230782836465633133163691622400), 44570725059472557570647659929600, 1223258028116538682215732820654080, 2086299881359085087218436429260800, 760216729436306253356335762636800, 1149329757848215021364238014684160, 870369159691922225208029129318400, 0, (-592225385725427827681282867200), 50879656464563007974204608665600, 995930582089190321531173359052800, 2172602782576101531853498473216000, 43532037124836055822332117504000, 656293602267506435003286177484800, 1170547673055622376304944721346560, 702415881433265668580601653990400, 228926562516330460384541376430080, 686605124552346207557462686003200, 636982543873836800552191119667200, 502111759980404001242380550307840, 31896305859398488425865034588160, 0]

private def f400desc12IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![9951140636915795912452722742135789977600]

theorem f400desc12_compression_check :
    f400desc12ᵀ*f412rawM4Form*f400desc12=f400desc12Form := by
  have hD : natFourIntegerMatrix 1 f400desc12IntegerCoordinates=f400desc12 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f400desc12IntegerCoordinates) (f400desc12) (by decide +kernel) a b
  have hV : f400desc12IntegerCoordinatesᵀ*f412rawInteger=f400desc12IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f400desc12IntegerCoordinatesᵀ*f412rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f400desc12IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f400desc12IntegerLeftProduct*f400desc12IntegerCoordinates=f400desc12IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc12IntegerLeftProduct*f400desc12IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc12IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc12IntegerForm=f400desc12Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc12IntegerForm) (f400desc12Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f412rawInteger f400desc12IntegerCoordinates f400desc12IntegerLeftProduct f400desc12IntegerForm
    f412rawM4Form f400desc12 f400desc12Form f412_raw_integer_check hD hV hY hF

theorem f400desc12_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[12] (natFourWordBlock f400basis (complexify b400relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[12]
          (natFourWordBlock f400basis (complexify b400relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f400desc12Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 12
    f400basis b400relative
    f412basis f400desc12 f412rawM4Form f400desc12Form
    f400desc12_actual f412_actual_raw_M4_matrix f400desc12_compression_check x y


#print axioms f400desc12_compression_check
#print axioms f400desc12_source_form
end TorusLean.BosonFiniteCertificate
