import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates402
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger404
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

def f402desc2Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1023734687610650330080499/15625000000000000000000)]

private def f402desc2IntegerCoordinates : Matrix (Fin 5) (Fin 1) ℤ :=
  !![(-1);
    (-4);
    (-1);
    4;
    2]

private def f402desc2IntegerLeftProduct : Matrix (Fin 1) (Fin 5) ℤ :=
  !![33282771664901193742863072, 4278532014442698914349484, 14936153011358884042491952, 14364896101256031303089488, 36696244168044184677773472]

private def f402desc2IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![65519020007081621125151936]

theorem f402desc2_compression_check :
    f402desc2ᵀ*f404rawM4Form*f402desc2=f402desc2Form := by
  have hD : natFourIntegerMatrix 1 f402desc2IntegerCoordinates=f402desc2 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f402desc2IntegerCoordinates) (f402desc2) (by decide +kernel) a b
  have hV : f402desc2IntegerCoordinatesᵀ*f404rawInteger=f402desc2IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 5) => (f402desc2IntegerCoordinatesᵀ*f404rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 5) => (f402desc2IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f402desc2IntegerLeftProduct*f402desc2IntegerCoordinates=f402desc2IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc2IntegerLeftProduct*f402desc2IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc2IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc2IntegerForm=f402desc2Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc2IntegerForm) (f402desc2Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f404rawInteger f402desc2IntegerCoordinates f402desc2IntegerLeftProduct f402desc2IntegerForm
    f404rawM4Form f402desc2 f402desc2Form f404_raw_integer_check hD hV hY hF

theorem f402desc2_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2] (natFourWordBlock f402basis (complexify b402relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
          (natFourWordBlock f402basis (complexify b402relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f402desc2Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 2
    f402basis b402relative
    f404basis f402desc2 f404rawM4Form f402desc2Form
    f402desc2_actual f404_actual_raw_M4_matrix f402desc2_compression_check x y


#print axioms f402desc2_compression_check
#print axioms f402desc2_source_form
end TorusLean.BosonFiniteCertificate
