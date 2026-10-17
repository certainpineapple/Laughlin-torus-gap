import torus.shared.BosonFiniteCertificateNatFourHS412Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

private theorem f412_S4_amplitude_row_0 : ∀ a : Fin 34,
    (natFourDoublePairRemoval 0 (12-0) (f412basis a) : ℚ)=f412S4Amplitudes 0 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 34) => (natFourDoublePairRemoval 0 (12-0) (f412basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 34) => f412S4Amplitudes 0 a) (by decide +kernel)
  exact h 0

private theorem f412_S4_amplitude_row_1 : ∀ a : Fin 34,
    (natFourDoublePairRemoval 1 (12-1) (f412basis a) : ℚ)=f412S4Amplitudes 1 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 34) => (natFourDoublePairRemoval 1 (12-1) (f412basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 34) => f412S4Amplitudes 1 a) (by decide +kernel)
  exact h 0

private theorem f412_S4_amplitude_row_2 : ∀ a : Fin 34,
    (natFourDoublePairRemoval 2 (12-2) (f412basis a) : ℚ)=f412S4Amplitudes 2 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 34) => (natFourDoublePairRemoval 2 (12-2) (f412basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 34) => f412S4Amplitudes 2 a) (by decide +kernel)
  exact h 0

private theorem f412_S4_amplitude_row_3 : ∀ a : Fin 34,
    (natFourDoublePairRemoval 3 (12-3) (f412basis a) : ℚ)=f412S4Amplitudes 3 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 34) => (natFourDoublePairRemoval 3 (12-3) (f412basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 34) => f412S4Amplitudes 3 a) (by decide +kernel)
  exact h 0

private theorem f412_S4_amplitude_row_4 : ∀ a : Fin 34,
    (natFourDoublePairRemoval 4 (12-4) (f412basis a) : ℚ)=f412S4Amplitudes 4 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 34) => (natFourDoublePairRemoval 4 (12-4) (f412basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 34) => f412S4Amplitudes 4 a) (by decide +kernel)
  exact h 0

private theorem f412_S4_amplitude_row_5 : ∀ a : Fin 34,
    (natFourDoublePairRemoval 5 (12-5) (f412basis a) : ℚ)=f412S4Amplitudes 5 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 34) => (natFourDoublePairRemoval 5 (12-5) (f412basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 34) => f412S4Amplitudes 5 a) (by decide +kernel)
  exact h 0

private theorem f412_S4_amplitude_row_6 : ∀ a : Fin 34,
    (natFourDoublePairRemoval 6 (12-6) (f412basis a) : ℚ)=f412S4Amplitudes 6 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 34) => (natFourDoublePairRemoval 6 (12-6) (f412basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 34) => f412S4Amplitudes 6 a) (by decide +kernel)
  exact h 0

private theorem f412_S4_amplitude_row_7 : ∀ a : Fin 34,
    (natFourDoublePairRemoval 7 (12-7) (f412basis a) : ℚ)=f412S4Amplitudes 7 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 34) => (natFourDoublePairRemoval 7 (12-7) (f412basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 34) => f412S4Amplitudes 7 a) (by decide +kernel)
  exact h 0

private theorem f412_S4_amplitude_row_8 : ∀ a : Fin 34,
    (natFourDoublePairRemoval 8 (12-8) (f412basis a) : ℚ)=f412S4Amplitudes 8 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 34) => (natFourDoublePairRemoval 8 (12-8) (f412basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 34) => f412S4Amplitudes 8 a) (by decide +kernel)
  exact h 0

private theorem f412_S4_amplitude_row_9 : ∀ a : Fin 34,
    (natFourDoublePairRemoval 9 (12-9) (f412basis a) : ℚ)=f412S4Amplitudes 9 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 34) => (natFourDoublePairRemoval 9 (12-9) (f412basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 34) => f412S4Amplitudes 9 a) (by decide +kernel)
  exact h 0

private theorem f412_S4_amplitude_row_10 : ∀ a : Fin 34,
    (natFourDoublePairRemoval 10 (12-10) (f412basis a) : ℚ)=f412S4Amplitudes 10 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 34) => (natFourDoublePairRemoval 10 (12-10) (f412basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 34) => f412S4Amplitudes 10 a) (by decide +kernel)
  exact h 0

private theorem f412_S4_amplitude_row_11 : ∀ a : Fin 34,
    (natFourDoublePairRemoval 11 (12-11) (f412basis a) : ℚ)=f412S4Amplitudes 11 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 34) => (natFourDoublePairRemoval 11 (12-11) (f412basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 34) => f412S4Amplitudes 11 a) (by decide +kernel)
  exact h 0

private theorem f412_S4_amplitude_row_12 : ∀ a : Fin 34,
    (natFourDoublePairRemoval 12 (12-12) (f412basis a) : ℚ)=f412S4Amplitudes 12 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 34) => (natFourDoublePairRemoval 12 (12-12) (f412basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 34) => f412S4Amplitudes 12 a) (by decide +kernel)
  exact h 0

theorem f412_S4_amplitudes_check : ∀ p : Fin 13, ∀ a : Fin 34,
    (natFourDoublePairRemoval p.val (12-p.val) (f412basis a) : ℚ)=f412S4Amplitudes p a := by
  intro p
  fin_cases p
  · exact f412_S4_amplitude_row_0
  · exact f412_S4_amplitude_row_1
  · exact f412_S4_amplitude_row_2
  · exact f412_S4_amplitude_row_3
  · exact f412_S4_amplitude_row_4
  · exact f412_S4_amplitude_row_5
  · exact f412_S4_amplitude_row_6
  · exact f412_S4_amplitude_row_7
  · exact f412_S4_amplitude_row_8
  · exact f412_S4_amplitude_row_9
  · exact f412_S4_amplitude_row_10
  · exact f412_S4_amplitude_row_11
  · exact f412_S4_amplitude_row_12

#print axioms f412_S4_amplitudes_check
end TorusLean.BosonFiniteCertificate
