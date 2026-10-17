import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourHSMatrixCore
import torus.shared.BosonFiniteCertificateNatFourHWordsSparse
import torus.shared.BosonFiniteCertificateNatFourS4AmplitudeCore
import torus.shared.BosonFiniteCertificateNatFourBasis404
import torus.shared.BosonFiniteCertificate404

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

def f404rawHForm : Matrix (Fin 5) (Fin 5) ℚ :=
  !![486, 18, 18, 0, 0;
    18, 48, 6, 6, 0;
    18, 6, 54, 8, 0;
    0, 6, 8, 18, 12;
    0, 0, 0, 12, 72]

def f404rawS4Form : Matrix (Fin 5) (Fin 5) ℚ :=
  !![108, 36, 36, 0, 0;
    36, 24, 12, 12, 0;
    36, 12, 28, 8, 24;
    0, 12, 8, 16, 12;
    0, 0, 24, 12, 36]

private theorem f404hs_shape (a : Fin 5) :
    (f404basis a).length=4 ∧ (f404basis a).sum=4 := by
  apply natFourBasis_shape 4
  rw [← f404_basis_enumeration]
  exact List.mem_ofFn.mpr ⟨a,rfl⟩

theorem f404_raw_H_matrix_check : ∀ a b : Fin 5,
    natFourHWordForm 4 (f404basis a) (f404basis b)=f404rawHForm a b := by
  have h := natFourRationalEntryCheck_sound
    (fun a b => natFourHWordFormSparse 4 (f404basis a) (f404basis b))
    f404rawHForm (by decide +kernel)
  intro a b
  simpa only [natFourHWordFormSparse_eq] using h a b


theorem f404_actual_raw_H_matrix (x y : Fin 5 → ℂ) :
    natOccupationInner (natFourWordBlock f404basis x)
      (canonicalPairHamiltonianNat (natFourWordBlock f404basis y))=
      star x ⬝ᵥ (complexify f404rawHForm *ᵥ y) :=
  canonicalNatFourH_matrix_form 4 f404basis (fun a => (f404hs_shape a).2)
    f404rawHForm f404_raw_H_matrix_check x y

theorem f404_relative_H_compression :
    b404relativeᵀ*f404rawHForm*b404relative=b404h := by
  decide +kernel

theorem f404_actual_relative_H_form (x y : Fin 2 → ℂ) :
    natOccupationInner (natFourWordBlock f404basis (complexify b404relative *ᵥ x))
      (canonicalPairHamiltonianNat (natFourWordBlock f404basis (complexify b404relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b404h *ᵥ y) :=
  natFour_operator_relative_matrix_form f404basis b404relative canonicalPairHamiltonianNat
    f404rawHForm b404h f404_actual_raw_H_matrix
    f404_relative_H_compression x y

def f404S4Amplitudes : Matrix (Fin 5) (Fin 5) ℚ :=
  !![12, 4, 4, 0, 0;
    0, 8, 0, 8, 0;
    0, 0, 16, 8, 24;
    0, 8, 0, 8, 0;
    12, 4, 4, 0, 0]

theorem f404_S4_amplitudes_check : ∀ p : Fin 5, ∀ a : Fin 5,
    (natFourDoublePairRemoval p.val (4-p.val) (f404basis a) : ℚ)=f404S4Amplitudes p a := by
  exact natFourRationalEntryCheck_sound
    (fun p a => (natFourDoublePairRemoval p.val (4-p.val) (f404basis a) : ℚ))
    f404S4Amplitudes (by decide +kernel)


theorem f404_S4_amplitude_gram_check :
    natFourS4AmplitudeGram 4 f404S4Amplitudes=f404rawS4Form := by
  decide +kernel

theorem f404_actual_raw_S4_matrix (x y : Fin 5 → ℂ) :
    natOccupationInner (natFourWordBlock f404basis x)
      (canonicalNatFourS4 (natFourWordBlock f404basis y))=
      star x ⬝ᵥ (complexify f404rawS4Form *ᵥ y) :=
  canonicalNatFourS4_amplitude_matrix_form 4 f404basis
    (fun a => (f404hs_shape a).1) (fun a => (f404hs_shape a).2)
    f404S4Amplitudes f404_S4_amplitudes_check f404rawS4Form f404_S4_amplitude_gram_check x y

theorem f404_relative_S4_compression :
    b404relativeᵀ*f404rawS4Form*b404relative=b404s := by
  decide +kernel

theorem f404_actual_relative_S4_form (x y : Fin 2 → ℂ) :
    natOccupationInner (natFourWordBlock f404basis (complexify b404relative *ᵥ x))
      (canonicalNatFourS4 (natFourWordBlock f404basis (complexify b404relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b404s *ᵥ y) :=
  natFour_operator_relative_matrix_form f404basis b404relative canonicalNatFourS4
    f404rawS4Form b404s f404_actual_raw_S4_matrix
    f404_relative_S4_compression x y

#print axioms f404_raw_H_matrix_check
#print axioms f404_actual_raw_H_matrix
#print axioms f404_relative_H_compression
#print axioms f404_actual_relative_H_form
#print axioms f404_S4_amplitudes_check
#print axioms f404_S4_amplitude_gram_check
#print axioms f404_actual_raw_S4_matrix
#print axioms f404_relative_S4_compression
#print axioms f404_actual_relative_S4_form
end TorusLean.BosonFiniteCertificate
