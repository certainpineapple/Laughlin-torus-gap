import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates403
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger405
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

def f403desc2Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(-26905389862516393050088911/200000000000000000000000)]

private def f403desc2IntegerCoordinates : Matrix (Fin 6) (Fin 1) ℤ :=
  !![1;
    3;
    (-6);
    0;
    (-6);
    8]

private def f403desc2IntegerLeftProduct : Matrix (Fin 1) (Fin 6) ℤ :=
  !![(-369079152191482061785722768), (-85604536750912294980393348), (-6728862340176045400613592), 14327691743007912173539512, (-1919892683597999815674048), 4486554381405851803424844]

private def f403desc2IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![(-538107797250327861001778220)]

theorem f403desc2_compression_check :
    f403desc2ᵀ*f405rawM4Form*f403desc2=f403desc2Form := by
  have hD : natFourIntegerMatrix 2 f403desc2IntegerCoordinates=f403desc2 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 2 f403desc2IntegerCoordinates) (f403desc2) (by decide +kernel) a b
  have hV : f403desc2IntegerCoordinatesᵀ*f405rawInteger=f403desc2IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 6) => (f403desc2IntegerCoordinatesᵀ*f405rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 6) => (f403desc2IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f403desc2IntegerLeftProduct*f403desc2IntegerCoordinates=f403desc2IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc2IntegerLeftProduct*f403desc2IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc2IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc2IntegerForm=f403desc2Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc2IntegerForm) (f403desc2Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 2
    f405rawInteger f403desc2IntegerCoordinates f403desc2IntegerLeftProduct f403desc2IntegerForm
    f405rawM4Form f403desc2 f403desc2Form f405_raw_integer_check hD hV hY hF

theorem f403desc2_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2] (natFourWordBlock f403basis (complexify b403relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
          (natFourWordBlock f403basis (complexify b403relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f403desc2Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 2
    f403basis b403relative
    f405basis f403desc2 f405rawM4Form f403desc2Form
    f403desc2_actual f405_actual_raw_M4_matrix f403desc2_compression_check x y


#print axioms f403desc2_compression_check
#print axioms f403desc2_source_form
end TorusLean.BosonFiniteCertificate
