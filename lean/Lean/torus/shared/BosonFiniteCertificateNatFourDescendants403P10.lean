import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates403
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger413
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
import torus.shared.BosonFiniteCertificate403

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

def f403desc10Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(59048898435341381874881225217663/156250000000000000000)]

private def f403desc10IntegerCoordinates : Matrix (Fin 39) (Fin 1) ℤ :=
  !![1;
    27;
    102;
    198;
    165;
    (-99);
    (-396);
    216;
    1404;
    2160;
    810;
    (-2592);
    (-2268);
    1830;
    3420;
    (-3240);
    (-11592);
    (-1440);
    (-17640);
    (-13104);
    (-17010);
    512;
    4320;
    5400;
    720;
    (-6048);
    9990;
    17280;
    (-7560);
    (-12096);
    0;
    (-30240);
    (-7350);
    6840;
    17640;
    3780;
    20160;
    18900;
    16800]

private def f403desc10IntegerLeftProduct : Matrix (Fin 1) (Fin 39) ℤ :=
  !![0, 0, 0, 0, 0, (-122054201132482518983738672601600), (-505660809022908270686776519488000), 0, 0, 0, (-513282850469152133975977881600), (-47723591164962250435982558169600), (-158055673425101995974390566323200), 0, 91231131882135294322405171200, (-7534802338887984489869387097600), (-41512010526496594647047836281600), 2628539889051598851488754470400, 491352199932291553415069337600, 5656266633901337359476853708800, (-15206368768663902164892473068800), 0, 0, (-260533784745413897113576857600), (-9205558610028571343311200691200), (-23157078681112690870604293228800), (-17097131726167365214181683200), 1446136942580583968421672537600, 6494674151581701700571712691200, 4340026379828268571779029836800, 3569835014379696437764579238400, (-2752904071234833418207251475200), 0, 1934490267250155938796404198400, (-2444140678451748817366069977600), (-9748658399174416186212413894400), 3362926425291186954321719635200, 0, 0]

private def f403desc10IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![1511651799944739375996959365572172800]

theorem f403desc10_compression_check :
    f403desc10ᵀ*f413rawM4Form*f403desc10=f403desc10Form := by
  have hD : natFourIntegerMatrix 2 f403desc10IntegerCoordinates=f403desc10 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 2 f403desc10IntegerCoordinates) (f403desc10) (by decide +kernel) a b
  have hV : f403desc10IntegerCoordinatesᵀ*f413rawInteger=f403desc10IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f403desc10IntegerCoordinatesᵀ*f413rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f403desc10IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f403desc10IntegerLeftProduct*f403desc10IntegerCoordinates=f403desc10IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc10IntegerLeftProduct*f403desc10IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc10IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc10IntegerForm=f403desc10Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc10IntegerForm) (f403desc10Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 2
    f413rawInteger f403desc10IntegerCoordinates f403desc10IntegerLeftProduct f403desc10IntegerForm
    f413rawM4Form f403desc10 f403desc10Form f413_raw_integer_check hD hV hY hF

theorem f403desc10_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[10] (natFourWordBlock f403basis (complexify b403relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[10]
          (natFourWordBlock f403basis (complexify b403relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f403desc10Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 10
    f403basis b403relative
    f413basis f403desc10 f413rawM4Form f403desc10Form
    f403desc10_actual f413_actual_raw_M4_matrix f403desc10_compression_check x y


#print axioms f403desc10_compression_check
#print axioms f403desc10_source_form
end TorusLean.BosonFiniteCertificate
