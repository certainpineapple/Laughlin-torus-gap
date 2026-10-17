import torus.shared.BosonFiniteCertificateNatFourHS411Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

private theorem f411_S4_amplitude_row_0 : ∀ a : Fin 27,
    (natFourDoublePairRemoval 0 (11-0) (f411basis a) : ℚ)=f411S4Amplitudes 0 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 27) => (natFourDoublePairRemoval 0 (11-0) (f411basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 27) => f411S4Amplitudes 0 a) (by decide +kernel)
  exact h 0

private theorem f411_S4_amplitude_row_1 : ∀ a : Fin 27,
    (natFourDoublePairRemoval 1 (11-1) (f411basis a) : ℚ)=f411S4Amplitudes 1 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 27) => (natFourDoublePairRemoval 1 (11-1) (f411basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 27) => f411S4Amplitudes 1 a) (by decide +kernel)
  exact h 0

private theorem f411_S4_amplitude_row_2 : ∀ a : Fin 27,
    (natFourDoublePairRemoval 2 (11-2) (f411basis a) : ℚ)=f411S4Amplitudes 2 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 27) => (natFourDoublePairRemoval 2 (11-2) (f411basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 27) => f411S4Amplitudes 2 a) (by decide +kernel)
  exact h 0

private theorem f411_S4_amplitude_row_3 : ∀ a : Fin 27,
    (natFourDoublePairRemoval 3 (11-3) (f411basis a) : ℚ)=f411S4Amplitudes 3 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 27) => (natFourDoublePairRemoval 3 (11-3) (f411basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 27) => f411S4Amplitudes 3 a) (by decide +kernel)
  exact h 0

private theorem f411_S4_amplitude_row_4 : ∀ a : Fin 27,
    (natFourDoublePairRemoval 4 (11-4) (f411basis a) : ℚ)=f411S4Amplitudes 4 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 27) => (natFourDoublePairRemoval 4 (11-4) (f411basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 27) => f411S4Amplitudes 4 a) (by decide +kernel)
  exact h 0

private theorem f411_S4_amplitude_row_5 : ∀ a : Fin 27,
    (natFourDoublePairRemoval 5 (11-5) (f411basis a) : ℚ)=f411S4Amplitudes 5 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 27) => (natFourDoublePairRemoval 5 (11-5) (f411basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 27) => f411S4Amplitudes 5 a) (by decide +kernel)
  exact h 0

private theorem f411_S4_amplitude_row_6 : ∀ a : Fin 27,
    (natFourDoublePairRemoval 6 (11-6) (f411basis a) : ℚ)=f411S4Amplitudes 6 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 27) => (natFourDoublePairRemoval 6 (11-6) (f411basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 27) => f411S4Amplitudes 6 a) (by decide +kernel)
  exact h 0

private theorem f411_S4_amplitude_row_7 : ∀ a : Fin 27,
    (natFourDoublePairRemoval 7 (11-7) (f411basis a) : ℚ)=f411S4Amplitudes 7 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 27) => (natFourDoublePairRemoval 7 (11-7) (f411basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 27) => f411S4Amplitudes 7 a) (by decide +kernel)
  exact h 0

private theorem f411_S4_amplitude_row_8 : ∀ a : Fin 27,
    (natFourDoublePairRemoval 8 (11-8) (f411basis a) : ℚ)=f411S4Amplitudes 8 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 27) => (natFourDoublePairRemoval 8 (11-8) (f411basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 27) => f411S4Amplitudes 8 a) (by decide +kernel)
  exact h 0

private theorem f411_S4_amplitude_row_9 : ∀ a : Fin 27,
    (natFourDoublePairRemoval 9 (11-9) (f411basis a) : ℚ)=f411S4Amplitudes 9 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 27) => (natFourDoublePairRemoval 9 (11-9) (f411basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 27) => f411S4Amplitudes 9 a) (by decide +kernel)
  exact h 0

private theorem f411_S4_amplitude_row_10 : ∀ a : Fin 27,
    (natFourDoublePairRemoval 10 (11-10) (f411basis a) : ℚ)=f411S4Amplitudes 10 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 27) => (natFourDoublePairRemoval 10 (11-10) (f411basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 27) => f411S4Amplitudes 10 a) (by decide +kernel)
  exact h 0

private theorem f411_S4_amplitude_row_11 : ∀ a : Fin 27,
    (natFourDoublePairRemoval 11 (11-11) (f411basis a) : ℚ)=f411S4Amplitudes 11 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 27) => (natFourDoublePairRemoval 11 (11-11) (f411basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 27) => f411S4Amplitudes 11 a) (by decide +kernel)
  exact h 0

theorem f411_S4_amplitudes_check : ∀ p : Fin 12, ∀ a : Fin 27,
    (natFourDoublePairRemoval p.val (11-p.val) (f411basis a) : ℚ)=f411S4Amplitudes p a := by
  intro p
  fin_cases p
  · exact f411_S4_amplitude_row_0
  · exact f411_S4_amplitude_row_1
  · exact f411_S4_amplitude_row_2
  · exact f411_S4_amplitude_row_3
  · exact f411_S4_amplitude_row_4
  · exact f411_S4_amplitude_row_5
  · exact f411_S4_amplitude_row_6
  · exact f411_S4_amplitude_row_7
  · exact f411_S4_amplitude_row_8
  · exact f411_S4_amplitude_row_9
  · exact f411_S4_amplitude_row_10
  · exact f411_S4_amplitude_row_11

#print axioms f411_S4_amplitudes_check
end TorusLean.BosonFiniteCertificate
