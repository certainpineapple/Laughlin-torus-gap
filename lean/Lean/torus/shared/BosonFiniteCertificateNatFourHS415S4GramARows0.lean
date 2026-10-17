import torus.shared.BosonFiniteCertificateNatFourHS415S4GramData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f415_S4Gram_hA_rows_0 (a : Fin 16) (hlo : 0 ≤ a.val) (hhi : a.val < 16) (b : Fin 54) :
    (natFourIntegerMatrix 1 f415S4GramAInt ) a b=( f415S4Amplitudes) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 1 f415S4GramAInt ) 0 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4Amplitudes) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 1 f415S4GramAInt ) 1 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4Amplitudes) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 1 f415S4GramAInt ) 2 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4Amplitudes) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 1 f415S4GramAInt ) 3 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4Amplitudes) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 1 f415S4GramAInt ) 4 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4Amplitudes) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 1 f415S4GramAInt ) 5 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4Amplitudes) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 1 f415S4GramAInt ) 6 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4Amplitudes) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 1 f415S4GramAInt ) 7 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4Amplitudes) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 1 f415S4GramAInt ) 8 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4Amplitudes) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 1 f415S4GramAInt ) 9 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4Amplitudes) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 1 f415S4GramAInt ) 10 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4Amplitudes) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 1 f415S4GramAInt ) 11 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4Amplitudes) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 1 f415S4GramAInt ) 12 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4Amplitudes) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 1 f415S4GramAInt ) 13 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4Amplitudes) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 1 f415S4GramAInt ) 14 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4Amplitudes) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 1 f415S4GramAInt ) 15 j)
      (fun (_ : Fin 1) (j : Fin 54) => ( f415S4Amplitudes) 15 j) (by decide +kernel)
    exact h 0 b

#print axioms f415_S4Gram_hA_rows_0
end TorusLean.BosonFiniteCertificate
