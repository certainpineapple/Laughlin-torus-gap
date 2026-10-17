import torus.shared.BosonFiniteCertificateNatFourHSMatrixCore
import torus.shared.BosonFiniteCertificateNatFourS4AmplitudeCore
import torus.shared.BosonFiniteCertificateNatFourBasis402
import torus.shared.BosonFiniteCertificate402

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

def f402rawHForm : Matrix (Fin 2) (Fin 2) ℚ :=
  !![54, 6;
    6, 22]

def f402rawS4Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![36, 12;
    12, 20]

private theorem f402hs_shape (a : Fin 2) :
    (f402basis a).length=4 ∧ (f402basis a).sum=2 := by
  apply natFourBasis_shape 2
  rw [← f402_basis_enumeration]
  exact List.mem_ofFn.mpr ⟨a,rfl⟩

theorem f402_raw_H_matrix_check : ∀ a b : Fin 2,
    natFourHWordForm 2 (f402basis a) (f402basis b)=f402rawHForm a b := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem f402_actual_raw_H_matrix (x y : Fin 2 → ℂ) :
    natOccupationInner (natFourWordBlock f402basis x)
      (canonicalPairHamiltonianNat (natFourWordBlock f402basis y))=
      star x ⬝ᵥ (complexify f402rawHForm *ᵥ y) :=
  canonicalNatFourH_matrix_form 2 f402basis (fun a => (f402hs_shape a).2)
    f402rawHForm f402_raw_H_matrix_check x y

theorem f402_relative_H_compression :
    b402relativeᵀ*f402rawHForm*b402relative=b402h := by
  decide +kernel

theorem f402_actual_relative_H_form (x y : Fin 1 → ℂ) :
    natOccupationInner (natFourWordBlock f402basis (complexify b402relative *ᵥ x))
      (canonicalPairHamiltonianNat (natFourWordBlock f402basis (complexify b402relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b402h *ᵥ y) :=
  natFour_operator_relative_matrix_form f402basis b402relative canonicalPairHamiltonianNat
    f402rawHForm b402h f402_actual_raw_H_matrix
    f402_relative_H_compression x y

def f402S4Amplitudes : Matrix (Fin 3) (Fin 2) ℚ :=
  !![12, 4;
    0, 16;
    12, 4]

theorem f402_S4_amplitudes_check : ∀ p : Fin 3, ∀ a : Fin 2,
    (natFourDoublePairRemoval p.val (2-p.val) (f402basis a) : ℚ)=f402S4Amplitudes p a := by
  intro p a
  fin_cases p <;> fin_cases a <;> decide +kernel

theorem f402_S4_amplitude_gram_check :
    natFourS4AmplitudeGram 2 f402S4Amplitudes=f402rawS4Form := by
  decide +kernel

theorem f402_actual_raw_S4_matrix (x y : Fin 2 → ℂ) :
    natOccupationInner (natFourWordBlock f402basis x)
      (canonicalNatFourS4 (natFourWordBlock f402basis y))=
      star x ⬝ᵥ (complexify f402rawS4Form *ᵥ y) :=
  canonicalNatFourS4_amplitude_matrix_form 2 f402basis
    (fun a => (f402hs_shape a).1) (fun a => (f402hs_shape a).2)
    f402S4Amplitudes f402_S4_amplitudes_check f402rawS4Form f402_S4_amplitude_gram_check x y

theorem f402_relative_S4_compression :
    b402relativeᵀ*f402rawS4Form*b402relative=b402s := by
  decide +kernel

theorem f402_actual_relative_S4_form (x y : Fin 1 → ℂ) :
    natOccupationInner (natFourWordBlock f402basis (complexify b402relative *ᵥ x))
      (canonicalNatFourS4 (natFourWordBlock f402basis (complexify b402relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b402s *ᵥ y) :=
  natFour_operator_relative_matrix_form f402basis b402relative canonicalNatFourS4
    f402rawS4Form b402s f402_actual_raw_S4_matrix
    f402_relative_S4_compression x y

#print axioms f402_raw_H_matrix_check
#print axioms f402_actual_raw_H_matrix
#print axioms f402_relative_H_compression
#print axioms f402_actual_relative_H_form
#print axioms f402_S4_amplitudes_check
#print axioms f402_S4_amplitude_gram_check
#print axioms f402_actual_raw_S4_matrix
#print axioms f402_relative_S4_compression
#print axioms f402_actual_relative_S4_form
end TorusLean.BosonFiniteCertificate
