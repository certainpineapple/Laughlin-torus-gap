import torus.shared.BosonFiniteCertificateNatFourHSMatrixCore
import torus.shared.BosonFiniteCertificateNatFourS4AmplitudeCore
import torus.shared.BosonFiniteCertificateNatFourBasis403
import torus.shared.BosonFiniteCertificate403

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

def f403rawHForm : Matrix (Fin 3) (Fin 3) ℚ :=
  !![135, 9, 0;
    9, 19, 6;
    0, 6, 27]

def f403rawS4Form : Matrix (Fin 3) (Fin 3) ℚ :=
  !![54, 18, 0;
    18, 14, 12;
    0, 12, 18]

private theorem f403hs_shape (a : Fin 3) :
    (f403basis a).length=4 ∧ (f403basis a).sum=3 := by
  apply natFourBasis_shape 3
  rw [← f403_basis_enumeration]
  exact List.mem_ofFn.mpr ⟨a,rfl⟩

theorem f403_raw_H_matrix_check : ∀ a b : Fin 3,
    natFourHWordForm 3 (f403basis a) (f403basis b)=f403rawHForm a b := by
  intro a b
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem f403_actual_raw_H_matrix (x y : Fin 3 → ℂ) :
    natOccupationInner (natFourWordBlock f403basis x)
      (canonicalPairHamiltonianNat (natFourWordBlock f403basis y))=
      star x ⬝ᵥ (complexify f403rawHForm *ᵥ y) :=
  canonicalNatFourH_matrix_form 3 f403basis (fun a => (f403hs_shape a).2)
    f403rawHForm f403_raw_H_matrix_check x y

theorem f403_relative_H_compression :
    b403relativeᵀ*f403rawHForm*b403relative=b403h := by
  decide +kernel

theorem f403_actual_relative_H_form (x y : Fin 1 → ℂ) :
    natOccupationInner (natFourWordBlock f403basis (complexify b403relative *ᵥ x))
      (canonicalPairHamiltonianNat (natFourWordBlock f403basis (complexify b403relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b403h *ᵥ y) :=
  natFour_operator_relative_matrix_form f403basis b403relative canonicalPairHamiltonianNat
    f403rawHForm b403h f403_actual_raw_H_matrix
    f403_relative_H_compression x y

def f403S4Amplitudes : Matrix (Fin 4) (Fin 3) ℚ :=
  !![12, 4, 0;
    0, 8, 12;
    0, 8, 12;
    12, 4, 0]

theorem f403_S4_amplitudes_check : ∀ p : Fin 4, ∀ a : Fin 3,
    (natFourDoublePairRemoval p.val (3-p.val) (f403basis a) : ℚ)=f403S4Amplitudes p a := by
  intro p a
  fin_cases p <;> fin_cases a <;> decide +kernel

theorem f403_S4_amplitude_gram_check :
    natFourS4AmplitudeGram 3 f403S4Amplitudes=f403rawS4Form := by
  decide +kernel

theorem f403_actual_raw_S4_matrix (x y : Fin 3 → ℂ) :
    natOccupationInner (natFourWordBlock f403basis x)
      (canonicalNatFourS4 (natFourWordBlock f403basis y))=
      star x ⬝ᵥ (complexify f403rawS4Form *ᵥ y) :=
  canonicalNatFourS4_amplitude_matrix_form 3 f403basis
    (fun a => (f403hs_shape a).1) (fun a => (f403hs_shape a).2)
    f403S4Amplitudes f403_S4_amplitudes_check f403rawS4Form f403_S4_amplitude_gram_check x y

theorem f403_relative_S4_compression :
    b403relativeᵀ*f403rawS4Form*b403relative=b403s := by
  decide +kernel

theorem f403_actual_relative_S4_form (x y : Fin 1 → ℂ) :
    natOccupationInner (natFourWordBlock f403basis (complexify b403relative *ᵥ x))
      (canonicalNatFourS4 (natFourWordBlock f403basis (complexify b403relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b403s *ᵥ y) :=
  natFour_operator_relative_matrix_form f403basis b403relative canonicalNatFourS4
    f403rawS4Form b403s f403_actual_raw_S4_matrix
    f403_relative_S4_compression x y

#print axioms f403_raw_H_matrix_check
#print axioms f403_actual_raw_H_matrix
#print axioms f403_relative_H_compression
#print axioms f403_actual_relative_H_form
#print axioms f403_S4_amplitudes_check
#print axioms f403_S4_amplitude_gram_check
#print axioms f403_actual_raw_S4_matrix
#print axioms f403_relative_S4_compression
#print axioms f403_actual_relative_S4_form
end TorusLean.BosonFiniteCertificate
