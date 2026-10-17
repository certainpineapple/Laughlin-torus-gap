import torus.shared.BosonFiniteCertificateNatFourHSMatrixCore
import torus.shared.BosonFiniteCertificateNatFourBasis400
import torus.shared.BosonFiniteCertificate400

/-! Independent degree-zero checks retain the physical occupation metric 24
and both original pair factors: H and S4 both have word cross-form 144. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

def f400rawHForm : Matrix (Fin 1) (Fin 1) ℚ := !![144]
def f400rawS4Form : Matrix (Fin 1) (Fin 1) ℚ := !![144]

theorem f400_raw_H_matrix_check : ∀ a b : Fin 1,
    natFourHWordForm 0 (f400basis a) (f400basis b)=f400rawHForm a b := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem f400_raw_S4_matrix_check : ∀ a b : Fin 1,
    natFourS4WordForm 0 (f400basis a) (f400basis b)=f400rawS4Form a b := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem f400_actual_raw_H_matrix (x y : Fin 1 → ℂ) :
    natOccupationInner (natFourWordBlock f400basis x)
      (canonicalPairHamiltonianNat (natFourWordBlock f400basis y))=
      star x ⬝ᵥ (complexify f400rawHForm *ᵥ y) := by
  apply canonicalNatFourH_matrix_form 0 f400basis _ f400rawHForm f400_raw_H_matrix_check x y
  intro a
  fin_cases a
  rfl

theorem f400_actual_raw_S4_matrix (x y : Fin 1 → ℂ) :
    natOccupationInner (natFourWordBlock f400basis x)
      (canonicalNatFourS4 (natFourWordBlock f400basis y))=
      star x ⬝ᵥ (complexify f400rawS4Form *ᵥ y) := by
  apply canonicalNatFourS4_matrix_form 0 f400basis _ _ f400rawS4Form
    f400_raw_S4_matrix_check x y
  · intro a; fin_cases a; rfl
  · intro a; fin_cases a; rfl

theorem f400_relative_H_compression :
    b400relativeᵀ*f400rawHForm*b400relative=b400h := by
  decide +kernel

theorem f400_relative_S4_compression :
    b400relativeᵀ*f400rawS4Form*b400relative=b400s := by
  decide +kernel

theorem f400_actual_relative_H_form (x y : Fin 1 → ℂ) :
    natOccupationInner (natFourWordBlock f400basis (complexify b400relative *ᵥ x))
      (canonicalPairHamiltonianNat (natFourWordBlock f400basis (complexify b400relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b400h *ᵥ y) :=
  natFour_operator_relative_matrix_form f400basis b400relative canonicalPairHamiltonianNat
    f400rawHForm b400h f400_actual_raw_H_matrix f400_relative_H_compression x y

theorem f400_actual_relative_S4_form (x y : Fin 1 → ℂ) :
    natOccupationInner (natFourWordBlock f400basis (complexify b400relative *ᵥ x))
      (canonicalNatFourS4 (natFourWordBlock f400basis (complexify b400relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b400s *ᵥ y) :=
  natFour_operator_relative_matrix_form f400basis b400relative canonicalNatFourS4
    f400rawS4Form b400s f400_actual_raw_S4_matrix f400_relative_S4_compression x y

#print axioms f400_raw_H_matrix_check
#print axioms f400_raw_S4_matrix_check
#print axioms f400_actual_raw_H_matrix
#print axioms f400_actual_raw_S4_matrix
#print axioms f400_relative_H_compression
#print axioms f400_relative_S4_compression
#print axioms f400_actual_relative_H_form
#print axioms f400_actual_relative_S4_form
end TorusLean.BosonFiniteCertificate
