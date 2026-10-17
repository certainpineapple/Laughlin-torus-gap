import torus.shared.BosonFiniteCertificateNatFourHS415Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

private theorem f415_S4_amplitude_row_9 : ∀ a : Fin 54,
    (natFourDoublePairRemoval 9 (15-9) (f415basis a) : ℚ)=f415S4Amplitudes 9 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 54) => (natFourDoublePairRemoval 9 (15-9) (f415basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 54) => f415S4Amplitudes 9 a) (by decide +kernel)
  exact h 0

private theorem f415_S4_amplitude_row_10 : ∀ a : Fin 54,
    (natFourDoublePairRemoval 10 (15-10) (f415basis a) : ℚ)=f415S4Amplitudes 10 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 54) => (natFourDoublePairRemoval 10 (15-10) (f415basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 54) => f415S4Amplitudes 10 a) (by decide +kernel)
  exact h 0

private theorem f415_S4_amplitude_row_11 : ∀ a : Fin 54,
    (natFourDoublePairRemoval 11 (15-11) (f415basis a) : ℚ)=f415S4Amplitudes 11 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 54) => (natFourDoublePairRemoval 11 (15-11) (f415basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 54) => f415S4Amplitudes 11 a) (by decide +kernel)
  exact h 0

private theorem f415_S4_amplitude_row_12 : ∀ a : Fin 54,
    (natFourDoublePairRemoval 12 (15-12) (f415basis a) : ℚ)=f415S4Amplitudes 12 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 54) => (natFourDoublePairRemoval 12 (15-12) (f415basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 54) => f415S4Amplitudes 12 a) (by decide +kernel)
  exact h 0

private theorem f415_S4_amplitude_row_13 : ∀ a : Fin 54,
    (natFourDoublePairRemoval 13 (15-13) (f415basis a) : ℚ)=f415S4Amplitudes 13 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 54) => (natFourDoublePairRemoval 13 (15-13) (f415basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 54) => f415S4Amplitudes 13 a) (by decide +kernel)
  exact h 0

private theorem f415_S4_amplitude_row_14 : ∀ a : Fin 54,
    (natFourDoublePairRemoval 14 (15-14) (f415basis a) : ℚ)=f415S4Amplitudes 14 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 54) => (natFourDoublePairRemoval 14 (15-14) (f415basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 54) => f415S4Amplitudes 14 a) (by decide +kernel)
  exact h 0

private theorem f415_S4_amplitude_row_15 : ∀ a : Fin 54,
    (natFourDoublePairRemoval 15 (15-15) (f415basis a) : ℚ)=f415S4Amplitudes 15 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 54) => (natFourDoublePairRemoval 15 (15-15) (f415basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 54) => f415S4Amplitudes 15 a) (by decide +kernel)
  exact h 0

theorem f415_S4_amplitude_rows_1 (p : Fin 16) (hlo : 9 ≤ p.val) (hhi : p.val < 16) : ∀ a : Fin 54,
    (natFourDoublePairRemoval p.val (15-p.val) (f415basis a) : ℚ)=f415S4Amplitudes p a := by
  fin_cases p
  · change 9 ≤ (0 : ℕ) at hlo
    omega
  · change 9 ≤ (1 : ℕ) at hlo
    omega
  · change 9 ≤ (2 : ℕ) at hlo
    omega
  · change 9 ≤ (3 : ℕ) at hlo
    omega
  · change 9 ≤ (4 : ℕ) at hlo
    omega
  · change 9 ≤ (5 : ℕ) at hlo
    omega
  · change 9 ≤ (6 : ℕ) at hlo
    omega
  · change 9 ≤ (7 : ℕ) at hlo
    omega
  · change 9 ≤ (8 : ℕ) at hlo
    omega
  · exact f415_S4_amplitude_row_9
  · exact f415_S4_amplitude_row_10
  · exact f415_S4_amplitude_row_11
  · exact f415_S4_amplitude_row_12
  · exact f415_S4_amplitude_row_13
  · exact f415_S4_amplitude_row_14
  · exact f415_S4_amplitude_row_15

#print axioms f415_S4_amplitude_rows_1
end TorusLean.BosonFiniteCertificate
