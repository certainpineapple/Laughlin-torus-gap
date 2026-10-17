import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates402
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger403
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
import torus.shared.BosonFiniteCertificate402

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

def f402desc1Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(802125368725673747545089/31250000000000000000000)]

private def f402desc1IntegerCoordinates : Matrix (Fin 3) (Fin 1) ℤ :=
  !![(-1);
    (-1);
    2]

private def f402desc1IntegerLeftProduct : Matrix (Fin 1) (Fin 3) ℤ :=
  !![(-11278124144760411321308676), (-74719270887176171307156), 7157584191786986214413508]

private def f402desc1IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![25668011799221559921442848]

theorem f402desc1_compression_check :
    f402desc1ᵀ*f403rawM4Form*f402desc1=f402desc1Form := by
  have hD : natFourIntegerMatrix 1 f402desc1IntegerCoordinates=f402desc1 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f402desc1IntegerCoordinates) (f402desc1) (by decide +kernel) a b
  have hV : f402desc1IntegerCoordinatesᵀ*f403rawInteger=f402desc1IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f402desc1IntegerCoordinatesᵀ*f403rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f402desc1IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f402desc1IntegerLeftProduct*f402desc1IntegerCoordinates=f402desc1IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc1IntegerLeftProduct*f402desc1IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc1IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc1IntegerForm=f402desc1Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc1IntegerForm) (f402desc1Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f403rawInteger f402desc1IntegerCoordinates f402desc1IntegerLeftProduct f402desc1IntegerForm
    f403rawM4Form f402desc1 f402desc1Form f403_raw_integer_check hD hV hY hF

theorem f402desc1_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1] (natFourWordBlock f402basis (complexify b402relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
          (natFourWordBlock f402basis (complexify b402relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f402desc1Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 1
    f402basis b402relative
    f403basis f402desc1 f403rawM4Form f402desc1Form
    f402desc1_actual f403_actual_raw_M4_matrix f402desc1_compression_check x y


#print axioms f402desc1_compression_check
#print axioms f402desc1_source_form
end TorusLean.BosonFiniteCertificate
