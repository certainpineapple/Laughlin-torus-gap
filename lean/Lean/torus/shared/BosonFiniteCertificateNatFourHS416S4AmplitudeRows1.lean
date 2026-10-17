import torus.shared.BosonFiniteCertificateNatFourHS416Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

private theorem f416_S4_amplitude_row_9 : ∀ a : Fin 64,
    (natFourDoublePairRemoval 9 (16-9) (f416basis a) : ℚ)=f416S4Amplitudes 9 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 64) => (natFourDoublePairRemoval 9 (16-9) (f416basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 64) => f416S4Amplitudes 9 a) (by decide +kernel)
  exact h 0

private theorem f416_S4_amplitude_row_10 : ∀ a : Fin 64,
    (natFourDoublePairRemoval 10 (16-10) (f416basis a) : ℚ)=f416S4Amplitudes 10 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 64) => (natFourDoublePairRemoval 10 (16-10) (f416basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 64) => f416S4Amplitudes 10 a) (by decide +kernel)
  exact h 0

private theorem f416_S4_amplitude_row_11 : ∀ a : Fin 64,
    (natFourDoublePairRemoval 11 (16-11) (f416basis a) : ℚ)=f416S4Amplitudes 11 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 64) => (natFourDoublePairRemoval 11 (16-11) (f416basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 64) => f416S4Amplitudes 11 a) (by decide +kernel)
  exact h 0

private theorem f416_S4_amplitude_row_12 : ∀ a : Fin 64,
    (natFourDoublePairRemoval 12 (16-12) (f416basis a) : ℚ)=f416S4Amplitudes 12 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 64) => (natFourDoublePairRemoval 12 (16-12) (f416basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 64) => f416S4Amplitudes 12 a) (by decide +kernel)
  exact h 0

private theorem f416_S4_amplitude_row_13 : ∀ a : Fin 64,
    (natFourDoublePairRemoval 13 (16-13) (f416basis a) : ℚ)=f416S4Amplitudes 13 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 64) => (natFourDoublePairRemoval 13 (16-13) (f416basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 64) => f416S4Amplitudes 13 a) (by decide +kernel)
  exact h 0

private theorem f416_S4_amplitude_row_14 : ∀ a : Fin 64,
    (natFourDoublePairRemoval 14 (16-14) (f416basis a) : ℚ)=f416S4Amplitudes 14 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 64) => (natFourDoublePairRemoval 14 (16-14) (f416basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 64) => f416S4Amplitudes 14 a) (by decide +kernel)
  exact h 0

private theorem f416_S4_amplitude_row_15 : ∀ a : Fin 64,
    (natFourDoublePairRemoval 15 (16-15) (f416basis a) : ℚ)=f416S4Amplitudes 15 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 64) => (natFourDoublePairRemoval 15 (16-15) (f416basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 64) => f416S4Amplitudes 15 a) (by decide +kernel)
  exact h 0

private theorem f416_S4_amplitude_row_16 : ∀ a : Fin 64,
    (natFourDoublePairRemoval 16 (16-16) (f416basis a) : ℚ)=f416S4Amplitudes 16 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 64) => (natFourDoublePairRemoval 16 (16-16) (f416basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 64) => f416S4Amplitudes 16 a) (by decide +kernel)
  exact h 0

theorem f416_S4_amplitude_rows_1 (p : Fin 17) (hlo : 9 ≤ p.val) (hhi : p.val < 17) : ∀ a : Fin 64,
    (natFourDoublePairRemoval p.val (16-p.val) (f416basis a) : ℚ)=f416S4Amplitudes p a := by
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
  · exact f416_S4_amplitude_row_9
  · exact f416_S4_amplitude_row_10
  · exact f416_S4_amplitude_row_11
  · exact f416_S4_amplitude_row_12
  · exact f416_S4_amplitude_row_13
  · exact f416_S4_amplitude_row_14
  · exact f416_S4_amplitude_row_15
  · exact f416_S4_amplitude_row_16

#print axioms f416_S4_amplitude_rows_1
end TorusLean.BosonFiniteCertificate
