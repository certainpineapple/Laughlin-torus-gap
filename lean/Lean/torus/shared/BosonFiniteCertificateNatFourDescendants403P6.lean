import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates403
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger409
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

def f403desc6Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(39676536167166930587560166817/3125000000000000000000)]

private def f403desc6IntegerCoordinates : Matrix (Fin 18) (Fin 1) ℤ :=
  !![1;
    15;
    24;
    0;
    (-42);
    60;
    120;
    (-120);
    (-150);
    (-36);
    (-480);
    (-120);
    68;
    180;
    (-60);
    180;
    120;
    240]

private def f403desc6IntegerLeftProduct : Matrix (Fin 1) (Fin 18) ℤ :=
  !![0, 26479329640228507378738475520, 29364026801103019507936310208, (-77211490309650015487842756672), (-139507345484619498023718472704), 15465632847576979967040444480, 18251968195868693297587777152, (-44798971021213880783160313056), (-75017676708500795816333285952), 3715994051932005669425721120, (-45981708306531027672577295232), (-40413966872086575357898332672), 8027116726089006507594850560, (-95174348481861483155398272), (-35775598089483467770309557120), (-14095607443700665592373526656), (-19541286566676926962022469312), (-2092399689394164272231655936)]

private def f403desc6IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![50785966293973671152077013525760]

theorem f403desc6_compression_check :
    f403desc6ᵀ*f409rawM4Form*f403desc6=f403desc6Form := by
  have hD : natFourIntegerMatrix 2 f403desc6IntegerCoordinates=f403desc6 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 2 f403desc6IntegerCoordinates) (f403desc6) (by decide +kernel) a b
  have hV : f403desc6IntegerCoordinatesᵀ*f409rawInteger=f403desc6IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 18) => (f403desc6IntegerCoordinatesᵀ*f409rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 18) => (f403desc6IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f403desc6IntegerLeftProduct*f403desc6IntegerCoordinates=f403desc6IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc6IntegerLeftProduct*f403desc6IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc6IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc6IntegerForm=f403desc6Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc6IntegerForm) (f403desc6Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 2
    f409rawInteger f403desc6IntegerCoordinates f403desc6IntegerLeftProduct f403desc6IntegerForm
    f409rawM4Form f403desc6 f403desc6Form f409_raw_integer_check hD hV hY hF

theorem f403desc6_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6] (natFourWordBlock f403basis (complexify b403relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6]
          (natFourWordBlock f403basis (complexify b403relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f403desc6Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 6
    f403basis b403relative
    f409basis f403desc6 f409rawM4Form f403desc6Form
    f403desc6_actual f409_actual_raw_M4_matrix f403desc6_compression_check x y


#print axioms f403desc6_compression_check
#print axioms f403desc6_source_form
end TorusLean.BosonFiniteCertificate
