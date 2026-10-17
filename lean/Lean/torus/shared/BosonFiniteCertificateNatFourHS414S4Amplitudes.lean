import torus.shared.BosonFiniteCertificateNatFourHS414Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

private theorem f414_S4_amplitude_row_0 : ∀ a : Fin 47,
    (natFourDoublePairRemoval 0 (14-0) (f414basis a) : ℚ)=f414S4Amplitudes 0 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 47) => (natFourDoublePairRemoval 0 (14-0) (f414basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 47) => f414S4Amplitudes 0 a) (by decide +kernel)
  exact h 0

private theorem f414_S4_amplitude_row_1 : ∀ a : Fin 47,
    (natFourDoublePairRemoval 1 (14-1) (f414basis a) : ℚ)=f414S4Amplitudes 1 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 47) => (natFourDoublePairRemoval 1 (14-1) (f414basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 47) => f414S4Amplitudes 1 a) (by decide +kernel)
  exact h 0

private theorem f414_S4_amplitude_row_2 : ∀ a : Fin 47,
    (natFourDoublePairRemoval 2 (14-2) (f414basis a) : ℚ)=f414S4Amplitudes 2 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 47) => (natFourDoublePairRemoval 2 (14-2) (f414basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 47) => f414S4Amplitudes 2 a) (by decide +kernel)
  exact h 0

private theorem f414_S4_amplitude_row_3 : ∀ a : Fin 47,
    (natFourDoublePairRemoval 3 (14-3) (f414basis a) : ℚ)=f414S4Amplitudes 3 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 47) => (natFourDoublePairRemoval 3 (14-3) (f414basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 47) => f414S4Amplitudes 3 a) (by decide +kernel)
  exact h 0

private theorem f414_S4_amplitude_row_4 : ∀ a : Fin 47,
    (natFourDoublePairRemoval 4 (14-4) (f414basis a) : ℚ)=f414S4Amplitudes 4 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 47) => (natFourDoublePairRemoval 4 (14-4) (f414basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 47) => f414S4Amplitudes 4 a) (by decide +kernel)
  exact h 0

private theorem f414_S4_amplitude_row_5 : ∀ a : Fin 47,
    (natFourDoublePairRemoval 5 (14-5) (f414basis a) : ℚ)=f414S4Amplitudes 5 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 47) => (natFourDoublePairRemoval 5 (14-5) (f414basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 47) => f414S4Amplitudes 5 a) (by decide +kernel)
  exact h 0

private theorem f414_S4_amplitude_row_6 : ∀ a : Fin 47,
    (natFourDoublePairRemoval 6 (14-6) (f414basis a) : ℚ)=f414S4Amplitudes 6 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 47) => (natFourDoublePairRemoval 6 (14-6) (f414basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 47) => f414S4Amplitudes 6 a) (by decide +kernel)
  exact h 0

private theorem f414_S4_amplitude_row_7 : ∀ a : Fin 47,
    (natFourDoublePairRemoval 7 (14-7) (f414basis a) : ℚ)=f414S4Amplitudes 7 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 47) => (natFourDoublePairRemoval 7 (14-7) (f414basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 47) => f414S4Amplitudes 7 a) (by decide +kernel)
  exact h 0

private theorem f414_S4_amplitude_row_8 : ∀ a : Fin 47,
    (natFourDoublePairRemoval 8 (14-8) (f414basis a) : ℚ)=f414S4Amplitudes 8 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 47) => (natFourDoublePairRemoval 8 (14-8) (f414basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 47) => f414S4Amplitudes 8 a) (by decide +kernel)
  exact h 0

private theorem f414_S4_amplitude_row_9 : ∀ a : Fin 47,
    (natFourDoublePairRemoval 9 (14-9) (f414basis a) : ℚ)=f414S4Amplitudes 9 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 47) => (natFourDoublePairRemoval 9 (14-9) (f414basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 47) => f414S4Amplitudes 9 a) (by decide +kernel)
  exact h 0

private theorem f414_S4_amplitude_row_10 : ∀ a : Fin 47,
    (natFourDoublePairRemoval 10 (14-10) (f414basis a) : ℚ)=f414S4Amplitudes 10 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 47) => (natFourDoublePairRemoval 10 (14-10) (f414basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 47) => f414S4Amplitudes 10 a) (by decide +kernel)
  exact h 0

private theorem f414_S4_amplitude_row_11 : ∀ a : Fin 47,
    (natFourDoublePairRemoval 11 (14-11) (f414basis a) : ℚ)=f414S4Amplitudes 11 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 47) => (natFourDoublePairRemoval 11 (14-11) (f414basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 47) => f414S4Amplitudes 11 a) (by decide +kernel)
  exact h 0

private theorem f414_S4_amplitude_row_12 : ∀ a : Fin 47,
    (natFourDoublePairRemoval 12 (14-12) (f414basis a) : ℚ)=f414S4Amplitudes 12 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 47) => (natFourDoublePairRemoval 12 (14-12) (f414basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 47) => f414S4Amplitudes 12 a) (by decide +kernel)
  exact h 0

private theorem f414_S4_amplitude_row_13 : ∀ a : Fin 47,
    (natFourDoublePairRemoval 13 (14-13) (f414basis a) : ℚ)=f414S4Amplitudes 13 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 47) => (natFourDoublePairRemoval 13 (14-13) (f414basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 47) => f414S4Amplitudes 13 a) (by decide +kernel)
  exact h 0

private theorem f414_S4_amplitude_row_14 : ∀ a : Fin 47,
    (natFourDoublePairRemoval 14 (14-14) (f414basis a) : ℚ)=f414S4Amplitudes 14 a := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (a : Fin 47) => (natFourDoublePairRemoval 14 (14-14) (f414basis a) : ℚ))
    (fun (_ : Fin 1) (a : Fin 47) => f414S4Amplitudes 14 a) (by decide +kernel)
  exact h 0

theorem f414_S4_amplitudes_check : ∀ p : Fin 15, ∀ a : Fin 47,
    (natFourDoublePairRemoval p.val (14-p.val) (f414basis a) : ℚ)=f414S4Amplitudes p a := by
  intro p
  fin_cases p
  · exact f414_S4_amplitude_row_0
  · exact f414_S4_amplitude_row_1
  · exact f414_S4_amplitude_row_2
  · exact f414_S4_amplitude_row_3
  · exact f414_S4_amplitude_row_4
  · exact f414_S4_amplitude_row_5
  · exact f414_S4_amplitude_row_6
  · exact f414_S4_amplitude_row_7
  · exact f414_S4_amplitude_row_8
  · exact f414_S4_amplitude_row_9
  · exact f414_S4_amplitude_row_10
  · exact f414_S4_amplitude_row_11
  · exact f414_S4_amplitude_row_12
  · exact f414_S4_amplitude_row_13
  · exact f414_S4_amplitude_row_14

#print axioms f414_S4_amplitudes_check
end TorusLean.BosonFiniteCertificate
