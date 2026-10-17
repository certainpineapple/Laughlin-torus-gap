import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates400
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger411
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

def f400desc11Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(4026514918305997193614919264690037/4882812500000000000)]

private def f400desc11IntegerCoordinates : Matrix (Fin 27) (Fin 1) ℤ :=
  !![4;
    132;
    660;
    1980;
    3960;
    5544;
    1320;
    11880;
    31680;
    55440;
    33264;
    23760;
    110880;
    166320;
    110880;
    138600;
    3960;
    47520;
    110880;
    166320;
    166320;
    665280;
    415800;
    554400;
    166320;
    831600;
    369600]

private def f400desc11IntegerLeftProduct : Matrix (Fin 1) (Fin 27) ℤ :=
  !![0, 0, 0, 639620500117529778466708825021440, 471446404065663603209073907361280, 866650793344507522786353818803200, 0, (-1373125959421029100980248371200), 55949161935156681662761189616640, 297528681058320416567888086871040, 905077829436555506209712024947200, (-4725909795081891171280100083200), 132264305746341206388761871498240, 534688938260548868921532771813120, 279661612341992336909531026122240, 316872131458195426058913009715200, (-798544707838390384583723827200), (-3252099921347165783577998515200), 107761299212228137767225210862080, 514544372957636415236174971288320, 89321126173884202591541503296000, 233394316690650510901512604561920, 275492262349841901038738964172800, 131973722909130391592480437201920, 207147253326642070700540658393600, 133861142968250935712237929774080, (-29928064362706816486226569797120)]

private def f400desc11IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![824630255269068225252335465408519577600]

theorem f400desc11_compression_check :
    f400desc11ᵀ*f411rawM4Form*f400desc11=f400desc11Form := by
  have hD : natFourIntegerMatrix 1 f400desc11IntegerCoordinates=f400desc11 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f400desc11IntegerCoordinates) (f400desc11) (by decide +kernel) a b
  have hV : f400desc11IntegerCoordinatesᵀ*f411rawInteger=f400desc11IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f400desc11IntegerCoordinatesᵀ*f411rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f400desc11IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f400desc11IntegerLeftProduct*f400desc11IntegerCoordinates=f400desc11IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc11IntegerLeftProduct*f400desc11IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc11IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc11IntegerForm=f400desc11Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc11IntegerForm) (f400desc11Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f411rawInteger f400desc11IntegerCoordinates f400desc11IntegerLeftProduct f400desc11IntegerForm
    f411rawM4Form f400desc11 f400desc11Form f411_raw_integer_check hD hV hY hF

theorem f400desc11_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[11] (natFourWordBlock f400basis (complexify b400relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[11]
          (natFourWordBlock f400basis (complexify b400relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f400desc11Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 11
    f400basis b400relative
    f411basis f400desc11 f411rawM4Form f400desc11Form
    f400desc11_actual f411_actual_raw_M4_matrix f400desc11_compression_check x y


#print axioms f400desc11_compression_check
#print axioms f400desc11_source_form
end TorusLean.BosonFiniteCertificate
