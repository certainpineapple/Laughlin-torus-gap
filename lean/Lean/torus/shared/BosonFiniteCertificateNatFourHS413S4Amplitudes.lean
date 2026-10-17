import torus.shared.BosonFiniteCertificateNatFourHS413Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

private theorem f413_S4_amplitude_row_0 : ∀ a : Fin 39,
    (natFourDoublePairRemoval 0 (13-0) (f413basis a) : ℚ)=f413S4Amplitudes 0 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 39) => (natFourDoublePairRemoval 0 (13-0) (f413basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 39) => f413S4Amplitudes 0 a) (by decide +kernel)
  exact h 0

private theorem f413_S4_amplitude_row_1 : ∀ a : Fin 39,
    (natFourDoublePairRemoval 1 (13-1) (f413basis a) : ℚ)=f413S4Amplitudes 1 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 39) => (natFourDoublePairRemoval 1 (13-1) (f413basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 39) => f413S4Amplitudes 1 a) (by decide +kernel)
  exact h 0

private theorem f413_S4_amplitude_row_2 : ∀ a : Fin 39,
    (natFourDoublePairRemoval 2 (13-2) (f413basis a) : ℚ)=f413S4Amplitudes 2 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 39) => (natFourDoublePairRemoval 2 (13-2) (f413basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 39) => f413S4Amplitudes 2 a) (by decide +kernel)
  exact h 0

private theorem f413_S4_amplitude_row_3 : ∀ a : Fin 39,
    (natFourDoublePairRemoval 3 (13-3) (f413basis a) : ℚ)=f413S4Amplitudes 3 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 39) => (natFourDoublePairRemoval 3 (13-3) (f413basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 39) => f413S4Amplitudes 3 a) (by decide +kernel)
  exact h 0

private theorem f413_S4_amplitude_row_4 : ∀ a : Fin 39,
    (natFourDoublePairRemoval 4 (13-4) (f413basis a) : ℚ)=f413S4Amplitudes 4 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 39) => (natFourDoublePairRemoval 4 (13-4) (f413basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 39) => f413S4Amplitudes 4 a) (by decide +kernel)
  exact h 0

private theorem f413_S4_amplitude_row_5 : ∀ a : Fin 39,
    (natFourDoublePairRemoval 5 (13-5) (f413basis a) : ℚ)=f413S4Amplitudes 5 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 39) => (natFourDoublePairRemoval 5 (13-5) (f413basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 39) => f413S4Amplitudes 5 a) (by decide +kernel)
  exact h 0

private theorem f413_S4_amplitude_row_6 : ∀ a : Fin 39,
    (natFourDoublePairRemoval 6 (13-6) (f413basis a) : ℚ)=f413S4Amplitudes 6 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 39) => (natFourDoublePairRemoval 6 (13-6) (f413basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 39) => f413S4Amplitudes 6 a) (by decide +kernel)
  exact h 0

private theorem f413_S4_amplitude_row_7 : ∀ a : Fin 39,
    (natFourDoublePairRemoval 7 (13-7) (f413basis a) : ℚ)=f413S4Amplitudes 7 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 39) => (natFourDoublePairRemoval 7 (13-7) (f413basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 39) => f413S4Amplitudes 7 a) (by decide +kernel)
  exact h 0

private theorem f413_S4_amplitude_row_8 : ∀ a : Fin 39,
    (natFourDoublePairRemoval 8 (13-8) (f413basis a) : ℚ)=f413S4Amplitudes 8 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 39) => (natFourDoublePairRemoval 8 (13-8) (f413basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 39) => f413S4Amplitudes 8 a) (by decide +kernel)
  exact h 0

private theorem f413_S4_amplitude_row_9 : ∀ a : Fin 39,
    (natFourDoublePairRemoval 9 (13-9) (f413basis a) : ℚ)=f413S4Amplitudes 9 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 39) => (natFourDoublePairRemoval 9 (13-9) (f413basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 39) => f413S4Amplitudes 9 a) (by decide +kernel)
  exact h 0

private theorem f413_S4_amplitude_row_10 : ∀ a : Fin 39,
    (natFourDoublePairRemoval 10 (13-10) (f413basis a) : ℚ)=f413S4Amplitudes 10 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 39) => (natFourDoublePairRemoval 10 (13-10) (f413basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 39) => f413S4Amplitudes 10 a) (by decide +kernel)
  exact h 0

private theorem f413_S4_amplitude_row_11 : ∀ a : Fin 39,
    (natFourDoublePairRemoval 11 (13-11) (f413basis a) : ℚ)=f413S4Amplitudes 11 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 39) => (natFourDoublePairRemoval 11 (13-11) (f413basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 39) => f413S4Amplitudes 11 a) (by decide +kernel)
  exact h 0

private theorem f413_S4_amplitude_row_12 : ∀ a : Fin 39,
    (natFourDoublePairRemoval 12 (13-12) (f413basis a) : ℚ)=f413S4Amplitudes 12 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 39) => (natFourDoublePairRemoval 12 (13-12) (f413basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 39) => f413S4Amplitudes 12 a) (by decide +kernel)
  exact h 0

private theorem f413_S4_amplitude_row_13 : ∀ a : Fin 39,
    (natFourDoublePairRemoval 13 (13-13) (f413basis a) : ℚ)=f413S4Amplitudes 13 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 39) => (natFourDoublePairRemoval 13 (13-13) (f413basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 39) => f413S4Amplitudes 13 a) (by decide +kernel)
  exact h 0

theorem f413_S4_amplitudes_check : ∀ p : Fin 14, ∀ a : Fin 39,
    (natFourDoublePairRemoval p.val (13-p.val) (f413basis a) : ℚ)=f413S4Amplitudes p a := by
  intro p
  fin_cases p
  · exact f413_S4_amplitude_row_0
  · exact f413_S4_amplitude_row_1
  · exact f413_S4_amplitude_row_2
  · exact f413_S4_amplitude_row_3
  · exact f413_S4_amplitude_row_4
  · exact f413_S4_amplitude_row_5
  · exact f413_S4_amplitude_row_6
  · exact f413_S4_amplitude_row_7
  · exact f413_S4_amplitude_row_8
  · exact f413_S4_amplitude_row_9
  · exact f413_S4_amplitude_row_10
  · exact f413_S4_amplitude_row_11
  · exact f413_S4_amplitude_row_12
  · exact f413_S4_amplitude_row_13

#print axioms f413_S4_amplitudes_check
end TorusLean.BosonFiniteCertificate
