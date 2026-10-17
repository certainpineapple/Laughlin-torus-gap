import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates400
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger406
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

def f400desc6Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(21788768195317306933560755379/390625000000000000000)]

private def f400desc6IntegerCoordinates : Matrix (Fin 9) (Fin 1) ℤ :=
  !![4;
    72;
    180;
    120;
    360;
    1440;
    360;
    480;
    1080]

private def f400desc6IntegerLeftProduct : Matrix (Fin 1) (Fin 9) ℤ :=
  !![1569527110456626568658417280, (-7705317122140245585105667680), 7976796334120118756456830656, 8239475309479483103449016256, 480277339409737553897271168, 17354425581454045454305883712, 20846022176825523153776461248, 7870176490634581330566607680, 16164505137446573360701304448]

private def f400desc6IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![55779246580012305749915533770240]

theorem f400desc6_compression_check :
    f400desc6ᵀ*f406rawM4Form*f400desc6=f400desc6Form := by
  have hD : natFourIntegerMatrix 1 f400desc6IntegerCoordinates=f400desc6 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f400desc6IntegerCoordinates) (f400desc6) (by decide +kernel) a b
  have hV : f400desc6IntegerCoordinatesᵀ*f406rawInteger=f400desc6IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 9) => (f400desc6IntegerCoordinatesᵀ*f406rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 9) => (f400desc6IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f400desc6IntegerLeftProduct*f400desc6IntegerCoordinates=f400desc6IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc6IntegerLeftProduct*f400desc6IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc6IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc6IntegerForm=f400desc6Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc6IntegerForm) (f400desc6Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f406rawInteger f400desc6IntegerCoordinates f400desc6IntegerLeftProduct f400desc6IntegerForm
    f406rawM4Form f400desc6 f400desc6Form f406_raw_integer_check hD hV hY hF

theorem f400desc6_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6] (natFourWordBlock f400basis (complexify b400relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6]
          (natFourWordBlock f400basis (complexify b400relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f400desc6Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 6
    f400basis b400relative
    f406basis f400desc6 f406rawM4Form f400desc6Form
    f400desc6_actual f406_actual_raw_M4_matrix f400desc6_compression_check x y


#print axioms f400desc6_compression_check
#print axioms f400desc6_source_form
end TorusLean.BosonFiniteCertificate
