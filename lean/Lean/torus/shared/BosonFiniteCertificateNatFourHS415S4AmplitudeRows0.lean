import torus.shared.BosonFiniteCertificateNatFourHS415Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

private theorem f415_S4_amplitude_row_0 : ∀ a : Fin 54,
    (natFourDoublePairRemoval 0 (15-0) (f415basis a) : ℚ)=f415S4Amplitudes 0 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 54) => (natFourDoublePairRemoval 0 (15-0) (f415basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 54) => f415S4Amplitudes 0 a) (by decide +kernel)
  exact h 0

private theorem f415_S4_amplitude_row_1 : ∀ a : Fin 54,
    (natFourDoublePairRemoval 1 (15-1) (f415basis a) : ℚ)=f415S4Amplitudes 1 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 54) => (natFourDoublePairRemoval 1 (15-1) (f415basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 54) => f415S4Amplitudes 1 a) (by decide +kernel)
  exact h 0

private theorem f415_S4_amplitude_row_2 : ∀ a : Fin 54,
    (natFourDoublePairRemoval 2 (15-2) (f415basis a) : ℚ)=f415S4Amplitudes 2 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 54) => (natFourDoublePairRemoval 2 (15-2) (f415basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 54) => f415S4Amplitudes 2 a) (by decide +kernel)
  exact h 0

private theorem f415_S4_amplitude_row_3 : ∀ a : Fin 54,
    (natFourDoublePairRemoval 3 (15-3) (f415basis a) : ℚ)=f415S4Amplitudes 3 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 54) => (natFourDoublePairRemoval 3 (15-3) (f415basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 54) => f415S4Amplitudes 3 a) (by decide +kernel)
  exact h 0

private theorem f415_S4_amplitude_row_4 : ∀ a : Fin 54,
    (natFourDoublePairRemoval 4 (15-4) (f415basis a) : ℚ)=f415S4Amplitudes 4 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 54) => (natFourDoublePairRemoval 4 (15-4) (f415basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 54) => f415S4Amplitudes 4 a) (by decide +kernel)
  exact h 0

private theorem f415_S4_amplitude_row_5 : ∀ a : Fin 54,
    (natFourDoublePairRemoval 5 (15-5) (f415basis a) : ℚ)=f415S4Amplitudes 5 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 54) => (natFourDoublePairRemoval 5 (15-5) (f415basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 54) => f415S4Amplitudes 5 a) (by decide +kernel)
  exact h 0

private theorem f415_S4_amplitude_row_6 : ∀ a : Fin 54,
    (natFourDoublePairRemoval 6 (15-6) (f415basis a) : ℚ)=f415S4Amplitudes 6 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 54) => (natFourDoublePairRemoval 6 (15-6) (f415basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 54) => f415S4Amplitudes 6 a) (by decide +kernel)
  exact h 0

private theorem f415_S4_amplitude_row_7 : ∀ a : Fin 54,
    (natFourDoublePairRemoval 7 (15-7) (f415basis a) : ℚ)=f415S4Amplitudes 7 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 54) => (natFourDoublePairRemoval 7 (15-7) (f415basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 54) => f415S4Amplitudes 7 a) (by decide +kernel)
  exact h 0

private theorem f415_S4_amplitude_row_8 : ∀ a : Fin 54,
    (natFourDoublePairRemoval 8 (15-8) (f415basis a) : ℚ)=f415S4Amplitudes 8 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 54) => (natFourDoublePairRemoval 8 (15-8) (f415basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 54) => f415S4Amplitudes 8 a) (by decide +kernel)
  exact h 0

theorem f415_S4_amplitude_rows_0 (p : Fin 16) (hlo : 0 ≤ p.val) (hhi : p.val < 9) : ∀ a : Fin 54,
    (natFourDoublePairRemoval p.val (15-p.val) (f415basis a) : ℚ)=f415S4Amplitudes p a := by
  fin_cases p
  · exact f415_S4_amplitude_row_0
  · exact f415_S4_amplitude_row_1
  · exact f415_S4_amplitude_row_2
  · exact f415_S4_amplitude_row_3
  · exact f415_S4_amplitude_row_4
  · exact f415_S4_amplitude_row_5
  · exact f415_S4_amplitude_row_6
  · exact f415_S4_amplitude_row_7
  · exact f415_S4_amplitude_row_8
  · change (9 : ℕ) < 9 at hhi
    omega
  · change (10 : ℕ) < 9 at hhi
    omega
  · change (11 : ℕ) < 9 at hhi
    omega
  · change (12 : ℕ) < 9 at hhi
    omega
  · change (13 : ℕ) < 9 at hhi
    omega
  · change (14 : ℕ) < 9 at hhi
    omega
  · change (15 : ℕ) < 9 at hhi
    omega

#print axioms f415_S4_amplitude_rows_0
end TorusLean.BosonFiniteCertificate
