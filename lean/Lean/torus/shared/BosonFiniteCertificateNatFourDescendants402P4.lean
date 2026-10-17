import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates402
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger406
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

def f402desc4Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(764838547512874882189229027/31250000000000000000000)]

private def f402desc4IntegerCoordinates : Matrix (Fin 9) (Fin 1) ℤ :=
  !![(-1);
    (-10);
    (-13);
    (-6);
    (-18);
    (-8);
    6;
    8;
    42]

private def f402desc4IntegerLeftProduct : Matrix (Fin 1) (Fin 9) ℤ :=
  !![1727653529541403035909552096, 135751010257595663574130328, (-212946720620165499509931248), (-47095488900522165297212784), (-236865548970964544315816416), 52807543412177136807511600, 198829748182592830365460176, 386370150733785209865344688, 390096610045673525046516192]

private def f402desc4IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![24474833520411996230055328864]

theorem f402desc4_compression_check :
    f402desc4ᵀ*f406rawM4Form*f402desc4=f402desc4Form := by
  have hD : natFourIntegerMatrix 1 f402desc4IntegerCoordinates=f402desc4 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f402desc4IntegerCoordinates) (f402desc4) (by decide +kernel) a b
  have hV : f402desc4IntegerCoordinatesᵀ*f406rawInteger=f402desc4IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 9) => (f402desc4IntegerCoordinatesᵀ*f406rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 9) => (f402desc4IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f402desc4IntegerLeftProduct*f402desc4IntegerCoordinates=f402desc4IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc4IntegerLeftProduct*f402desc4IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc4IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc4IntegerForm=f402desc4Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc4IntegerForm) (f402desc4Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f406rawInteger f402desc4IntegerCoordinates f402desc4IntegerLeftProduct f402desc4IntegerForm
    f406rawM4Form f402desc4 f402desc4Form f406_raw_integer_check hD hV hY hF

theorem f402desc4_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4] (natFourWordBlock f402basis (complexify b402relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
          (natFourWordBlock f402basis (complexify b402relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f402desc4Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 4
    f402basis b402relative
    f406basis f402desc4 f406rawM4Form f402desc4Form
    f402desc4_actual f406_actual_raw_M4_matrix f402desc4_compression_check x y


#print axioms f402desc4_compression_check
#print axioms f402desc4_source_form
end TorusLean.BosonFiniteCertificate
