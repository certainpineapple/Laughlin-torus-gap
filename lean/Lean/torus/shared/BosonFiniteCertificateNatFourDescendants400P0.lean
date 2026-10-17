import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates400
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger400
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

def f400desc0Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(78991706082567171822759/1953125000000000000000)]

private def f400desc0IntegerCoordinates : Matrix (Fin 1) (Fin 1) ℤ :=
  !![1]

private def f400desc0IntegerLeftProduct : Matrix (Fin 1) (Fin 1) ℤ :=
  !![40443753514274391973252608]

private def f400desc0IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![40443753514274391973252608]

theorem f400desc0_compression_check :
    f400desc0ᵀ*f400rawM4Form*f400desc0=f400desc0Form := by
  have hD : natFourIntegerMatrix 1 f400desc0IntegerCoordinates=f400desc0 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f400desc0IntegerCoordinates) (f400desc0) (by decide +kernel) a b
  have hV : f400desc0IntegerCoordinatesᵀ*f400rawInteger=f400desc0IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc0IntegerCoordinatesᵀ*f400rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc0IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f400desc0IntegerLeftProduct*f400desc0IntegerCoordinates=f400desc0IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc0IntegerLeftProduct*f400desc0IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc0IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc0IntegerForm=f400desc0Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc0IntegerForm) (f400desc0Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f400rawInteger f400desc0IntegerCoordinates f400desc0IntegerLeftProduct f400desc0IntegerForm
    f400rawM4Form f400desc0 f400desc0Form f400_raw_integer_check hD hV hY hF

#print axioms f400desc0_compression_check

theorem f400desc0_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0] (natFourWordBlock f400basis (complexify b400relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
          (natFourWordBlock f400basis (complexify b400relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f400desc0Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 0
    f400basis b400relative
    f400basis f400desc0 f400rawM4Form f400desc0Form
    f400desc0_actual f400_actual_raw_M4_matrix f400desc0_compression_check x y


#print axioms f400desc0_source_form
end TorusLean.BosonFiniteCertificate
