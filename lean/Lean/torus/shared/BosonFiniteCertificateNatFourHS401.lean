import torus.shared.BosonFiniteCertificateNatFourHSMatrixCore
import torus.shared.BosonFiniteCertificateNatFourS4AmplitudeCore
import torus.shared.BosonFiniteCertificateNatFourBasis401
import torus.shared.BosonFiniteCertificate401

/-! Independently checked genuine H/S4 source word forms and their original
relative compressions. Repeated-particle factorials and pair halves are part
of the source evaluator, not assumptions on these numerical tables. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

def f401rawHForm : Matrix (Fin 1) (Fin 1) ℚ :=
  !![36]

def f401rawS4Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![36]

private theorem f401hs_shape (a : Fin 1) :
    (f401basis a).length=4 ∧ (f401basis a).sum=1 := by
  apply natFourBasis_shape 1
  rw [← f401_basis_enumeration]
  exact List.mem_ofFn.mpr ⟨a,rfl⟩

theorem f401_raw_H_matrix_check : ∀ a b : Fin 1,
    natFourHWordForm 1 (f401basis a) (f401basis b)=f401rawHForm a b := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem f401_actual_raw_H_matrix (x y : Fin 1 → ℂ) :
    natOccupationInner (natFourWordBlock f401basis x)
      (canonicalPairHamiltonianNat (natFourWordBlock f401basis y))=
      star x ⬝ᵥ (complexify f401rawHForm *ᵥ y) :=
  canonicalNatFourH_matrix_form 1 f401basis (fun a => (f401hs_shape a).2)
    f401rawHForm f401_raw_H_matrix_check x y

theorem f401_relative_H_compression :
    b401relativeᵀ*f401rawHForm*b401relative=b401h := by
  decide +kernel

theorem f401_actual_relative_H_form (x y : Fin 0 → ℂ) :
    natOccupationInner (natFourWordBlock f401basis (complexify b401relative *ᵥ x))
      (canonicalPairHamiltonianNat (natFourWordBlock f401basis (complexify b401relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b401h *ᵥ y) :=
  natFour_operator_relative_matrix_form f401basis b401relative canonicalPairHamiltonianNat
    f401rawHForm b401h f401_actual_raw_H_matrix
    f401_relative_H_compression x y

def f401S4Amplitudes : Matrix (Fin 2) (Fin 1) ℚ :=
  !![12;
    12]

theorem f401_S4_amplitudes_check : ∀ p : Fin 2, ∀ a : Fin 1,
    (natFourDoublePairRemoval p.val (1-p.val) (f401basis a) : ℚ)=f401S4Amplitudes p a := by
  intro p a
  fin_cases p <;> fin_cases a <;> decide +kernel

theorem f401_S4_amplitude_gram_check :
    natFourS4AmplitudeGram 1 f401S4Amplitudes=f401rawS4Form := by
  decide +kernel

theorem f401_actual_raw_S4_matrix (x y : Fin 1 → ℂ) :
    natOccupationInner (natFourWordBlock f401basis x)
      (canonicalNatFourS4 (natFourWordBlock f401basis y))=
      star x ⬝ᵥ (complexify f401rawS4Form *ᵥ y) :=
  canonicalNatFourS4_amplitude_matrix_form 1 f401basis
    (fun a => (f401hs_shape a).1) (fun a => (f401hs_shape a).2)
    f401S4Amplitudes f401_S4_amplitudes_check f401rawS4Form f401_S4_amplitude_gram_check x y

theorem f401_relative_S4_compression :
    b401relativeᵀ*f401rawS4Form*b401relative=b401s := by
  decide +kernel

theorem f401_actual_relative_S4_form (x y : Fin 0 → ℂ) :
    natOccupationInner (natFourWordBlock f401basis (complexify b401relative *ᵥ x))
      (canonicalNatFourS4 (natFourWordBlock f401basis (complexify b401relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b401s *ᵥ y) :=
  natFour_operator_relative_matrix_form f401basis b401relative canonicalNatFourS4
    f401rawS4Form b401s f401_actual_raw_S4_matrix
    f401_relative_S4_compression x y

#print axioms f401_raw_H_matrix_check
#print axioms f401_actual_raw_H_matrix
#print axioms f401_relative_H_compression
#print axioms f401_actual_relative_H_form
#print axioms f401_S4_amplitudes_check
#print axioms f401_S4_amplitude_gram_check
#print axioms f401_actual_raw_S4_matrix
#print axioms f401_relative_S4_compression
#print axioms f401_actual_relative_S4_form
end TorusLean.BosonFiniteCertificate
