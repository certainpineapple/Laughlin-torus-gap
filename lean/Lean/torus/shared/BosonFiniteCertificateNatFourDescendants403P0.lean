import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates403
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger403
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

def f403desc0Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(-1286918764105179576183903/125000000000000000000000)]

private def f403desc0IntegerCoordinates : Matrix (Fin 3) (Fin 1) ℤ :=
  !![1;
    (-3);
    2]

private def f403desc0IntegerLeftProduct : Matrix (Fin 1) (Fin 3) ℤ :=
  !![(-13336096152875757205397004), 8885205098544660824265348, (-594844501428003379845924)]

private def f403desc0IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![(-41181400451365746437884896)]

theorem f403desc0_compression_check :
    f403desc0ᵀ*f403rawM4Form*f403desc0=f403desc0Form := by
  have hD : natFourIntegerMatrix 2 f403desc0IntegerCoordinates=f403desc0 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 2 f403desc0IntegerCoordinates) (f403desc0) (by decide +kernel) a b
  have hV : f403desc0IntegerCoordinatesᵀ*f403rawInteger=f403desc0IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f403desc0IntegerCoordinatesᵀ*f403rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f403desc0IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f403desc0IntegerLeftProduct*f403desc0IntegerCoordinates=f403desc0IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc0IntegerLeftProduct*f403desc0IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc0IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc0IntegerForm=f403desc0Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc0IntegerForm) (f403desc0Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 2
    f403rawInteger f403desc0IntegerCoordinates f403desc0IntegerLeftProduct f403desc0IntegerForm
    f403rawM4Form f403desc0 f403desc0Form f403_raw_integer_check hD hV hY hF

theorem f403desc0_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0] (natFourWordBlock f403basis (complexify b403relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
          (natFourWordBlock f403basis (complexify b403relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f403desc0Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 0
    f403basis b403relative
    f403basis f403desc0 f403rawM4Form f403desc0Form
    f403desc0_actual f403_actual_raw_M4_matrix f403desc0_compression_check x y


#print axioms f403desc0_compression_check
#print axioms f403desc0_source_form
end TorusLean.BosonFiniteCertificate
