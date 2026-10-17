import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import torus.shared.BosonFiniteCertificateNatFourHSMatrixCore
import torus.shared.BosonFiniteCertificateNatFourHWordsSparse
import torus.shared.BosonFiniteCertificateNatFourS4AmplitudeCore
import torus.shared.BosonFiniteCertificateNatFourBasis405
import torus.shared.BosonFiniteCertificate405

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

def f405rawHForm : Matrix (Fin 6) (Fin 6) ℚ :=
  !![2295, 45, 45, 0, 0, 0;
    45, 171, 15, 12, 6, 0;
    45, 15, 75, 12, 12, 0;
    0, 12, 12, 45, 6, 9;
    0, 6, 12, 6, 31, 12;
    0, 0, 0, 9, 12, 45]

def f405rawS4Form : Matrix (Fin 6) (Fin 6) ℚ :=
  !![270, 90, 90, 0, 0, 0;
    90, 54, 30, 24, 12, 0;
    90, 30, 42, 6, 12, 18;
    0, 24, 6, 27, 18, 9;
    0, 12, 12, 18, 18, 18;
    0, 0, 18, 9, 18, 27]

private theorem f405hs_shape (a : Fin 6) :
    (f405basis a).length=4 ∧ (f405basis a).sum=5 := by
  apply natFourBasis_shape 5
  rw [← f405_basis_enumeration]
  exact List.mem_ofFn.mpr ⟨a,rfl⟩

theorem f405_raw_H_matrix_check : ∀ a b : Fin 6,
    natFourHWordForm 5 (f405basis a) (f405basis b)=f405rawHForm a b := by
  have h := natFourRationalEntryCheck_sound
    (fun a b => natFourHWordFormSparse 5 (f405basis a) (f405basis b))
    f405rawHForm (by decide +kernel)
  intro a b
  simpa only [natFourHWordFormSparse_eq] using h a b


theorem f405_actual_raw_H_matrix (x y : Fin 6 → ℂ) :
    natOccupationInner (natFourWordBlock f405basis x)
      (canonicalPairHamiltonianNat (natFourWordBlock f405basis y))=
      star x ⬝ᵥ (complexify f405rawHForm *ᵥ y) :=
  canonicalNatFourH_matrix_form 5 f405basis (fun a => (f405hs_shape a).2)
    f405rawHForm f405_raw_H_matrix_check x y

theorem f405_relative_H_compression :
    b405relativeᵀ*f405rawHForm*b405relative=b405h := by
  decide +kernel

theorem f405_actual_relative_H_form (x y : Fin 1 → ℂ) :
    natOccupationInner (natFourWordBlock f405basis (complexify b405relative *ᵥ x))
      (canonicalPairHamiltonianNat (natFourWordBlock f405basis (complexify b405relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b405h *ᵥ y) :=
  natFour_operator_relative_matrix_form f405basis b405relative canonicalPairHamiltonianNat
    f405rawHForm b405h f405_actual_raw_H_matrix
    f405_relative_H_compression x y

def f405S4Amplitudes : Matrix (Fin 6) (Fin 6) ℚ :=
  !![12, 4, 4, 0, 0, 0;
    0, 8, 0, 8, 4, 0;
    0, 0, 8, 4, 8, 12;
    0, 0, 8, 4, 8, 12;
    0, 8, 0, 8, 4, 0;
    12, 4, 4, 0, 0, 0]

theorem f405_S4_amplitudes_check : ∀ p : Fin 6, ∀ a : Fin 6,
    (natFourDoublePairRemoval p.val (5-p.val) (f405basis a) : ℚ)=f405S4Amplitudes p a := by
  exact natFourRationalEntryCheck_sound
    (fun p a => (natFourDoublePairRemoval p.val (5-p.val) (f405basis a) : ℚ))
    f405S4Amplitudes (by decide +kernel)


theorem f405_S4_amplitude_gram_check :
    natFourS4AmplitudeGram 5 f405S4Amplitudes=f405rawS4Form := by
  decide +kernel

theorem f405_actual_raw_S4_matrix (x y : Fin 6 → ℂ) :
    natOccupationInner (natFourWordBlock f405basis x)
      (canonicalNatFourS4 (natFourWordBlock f405basis y))=
      star x ⬝ᵥ (complexify f405rawS4Form *ᵥ y) :=
  canonicalNatFourS4_amplitude_matrix_form 5 f405basis
    (fun a => (f405hs_shape a).1) (fun a => (f405hs_shape a).2)
    f405S4Amplitudes f405_S4_amplitudes_check f405rawS4Form f405_S4_amplitude_gram_check x y

theorem f405_relative_S4_compression :
    b405relativeᵀ*f405rawS4Form*b405relative=b405s := by
  decide +kernel

theorem f405_actual_relative_S4_form (x y : Fin 1 → ℂ) :
    natOccupationInner (natFourWordBlock f405basis (complexify b405relative *ᵥ x))
      (canonicalNatFourS4 (natFourWordBlock f405basis (complexify b405relative *ᵥ y)))=
      star x ⬝ᵥ (complexify b405s *ᵥ y) :=
  natFour_operator_relative_matrix_form f405basis b405relative canonicalNatFourS4
    f405rawS4Form b405s f405_actual_raw_S4_matrix
    f405_relative_S4_compression x y

#print axioms f405_raw_H_matrix_check
#print axioms f405_actual_raw_H_matrix
#print axioms f405_relative_H_compression
#print axioms f405_actual_relative_H_form
#print axioms f405_S4_amplitudes_check
#print axioms f405_S4_amplitude_gram_check
#print axioms f405_actual_raw_S4_matrix
#print axioms f405_relative_S4_compression
#print axioms f405_actual_relative_S4_form
end TorusLean.BosonFiniteCertificate
