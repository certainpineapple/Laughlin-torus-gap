import torus.shared.BosonFiniteCertificateNatFourHS416Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

private theorem f416_S4_amplitude_row_0 : ∀ a : Fin 64,
    (natFourDoublePairRemoval 0 (16-0) (f416basis a) : ℚ)=f416S4Amplitudes 0 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 64) => (natFourDoublePairRemoval 0 (16-0) (f416basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 64) => f416S4Amplitudes 0 a) (by decide +kernel)
  exact h 0

private theorem f416_S4_amplitude_row_1 : ∀ a : Fin 64,
    (natFourDoublePairRemoval 1 (16-1) (f416basis a) : ℚ)=f416S4Amplitudes 1 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 64) => (natFourDoublePairRemoval 1 (16-1) (f416basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 64) => f416S4Amplitudes 1 a) (by decide +kernel)
  exact h 0

private theorem f416_S4_amplitude_row_2 : ∀ a : Fin 64,
    (natFourDoublePairRemoval 2 (16-2) (f416basis a) : ℚ)=f416S4Amplitudes 2 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 64) => (natFourDoublePairRemoval 2 (16-2) (f416basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 64) => f416S4Amplitudes 2 a) (by decide +kernel)
  exact h 0

private theorem f416_S4_amplitude_row_3 : ∀ a : Fin 64,
    (natFourDoublePairRemoval 3 (16-3) (f416basis a) : ℚ)=f416S4Amplitudes 3 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 64) => (natFourDoublePairRemoval 3 (16-3) (f416basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 64) => f416S4Amplitudes 3 a) (by decide +kernel)
  exact h 0

private theorem f416_S4_amplitude_row_4 : ∀ a : Fin 64,
    (natFourDoublePairRemoval 4 (16-4) (f416basis a) : ℚ)=f416S4Amplitudes 4 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 64) => (natFourDoublePairRemoval 4 (16-4) (f416basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 64) => f416S4Amplitudes 4 a) (by decide +kernel)
  exact h 0

private theorem f416_S4_amplitude_row_5 : ∀ a : Fin 64,
    (natFourDoublePairRemoval 5 (16-5) (f416basis a) : ℚ)=f416S4Amplitudes 5 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 64) => (natFourDoublePairRemoval 5 (16-5) (f416basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 64) => f416S4Amplitudes 5 a) (by decide +kernel)
  exact h 0

private theorem f416_S4_amplitude_row_6 : ∀ a : Fin 64,
    (natFourDoublePairRemoval 6 (16-6) (f416basis a) : ℚ)=f416S4Amplitudes 6 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 64) => (natFourDoublePairRemoval 6 (16-6) (f416basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 64) => f416S4Amplitudes 6 a) (by decide +kernel)
  exact h 0

private theorem f416_S4_amplitude_row_7 : ∀ a : Fin 64,
    (natFourDoublePairRemoval 7 (16-7) (f416basis a) : ℚ)=f416S4Amplitudes 7 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 64) => (natFourDoublePairRemoval 7 (16-7) (f416basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 64) => f416S4Amplitudes 7 a) (by decide +kernel)
  exact h 0

private theorem f416_S4_amplitude_row_8 : ∀ a : Fin 64,
    (natFourDoublePairRemoval 8 (16-8) (f416basis a) : ℚ)=f416S4Amplitudes 8 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 64) => (natFourDoublePairRemoval 8 (16-8) (f416basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 64) => f416S4Amplitudes 8 a) (by decide +kernel)
  exact h 0

theorem f416_S4_amplitude_rows_0 (p : Fin 17) (hlo : 0 ≤ p.val) (hhi : p.val < 9) : ∀ a : Fin 64,
    (natFourDoublePairRemoval p.val (16-p.val) (f416basis a) : ℚ)=f416S4Amplitudes p a := by
  fin_cases p
  · exact f416_S4_amplitude_row_0
  · exact f416_S4_amplitude_row_1
  · exact f416_S4_amplitude_row_2
  · exact f416_S4_amplitude_row_3
  · exact f416_S4_amplitude_row_4
  · exact f416_S4_amplitude_row_5
  · exact f416_S4_amplitude_row_6
  · exact f416_S4_amplitude_row_7
  · exact f416_S4_amplitude_row_8
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
  · change (16 : ℕ) < 9 at hhi
    omega

#print axioms f416_S4_amplitude_rows_0
end TorusLean.BosonFiniteCertificate
