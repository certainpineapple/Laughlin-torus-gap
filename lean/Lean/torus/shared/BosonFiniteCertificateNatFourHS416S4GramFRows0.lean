import torus.shared.BosonFiniteCertificateNatFourHS416S4GramData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f416_S4Gram_hF_rows_0 (a : Fin 64) (hlo : 0 ≤ a.val) (hhi : a.val < 64) (b : Fin 64) :
    (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) a b=( f416rawS4Form) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 0 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 1 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 2 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 3 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 4 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 5 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 6 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 7 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 8 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 9 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 10 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 11 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 12 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 13 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 14 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 15 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 15 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 16 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 17 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 17 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 18 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 18 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 19 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 19 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 20 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 20 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 21 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 21 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 22 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 22 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 23 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 23 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 24 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 24 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 25 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 25 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 26 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 26 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 27 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 27 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 28 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 28 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 29 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 29 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 30 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 30 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 31 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 31 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 32 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 32 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 33 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 33 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 34 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 34 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 35 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 35 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 36 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 36 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 37 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 37 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 38 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 38 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 39 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 39 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 40 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 40 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 41 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 41 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 42 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 42 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 43 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 43 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 44 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 44 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 45 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 45 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 46 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 46 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 47 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 47 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 48 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 48 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 49 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 49 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 50 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 50 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 51 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 51 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 52 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 52 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 53 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 53 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 54 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 54 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 55 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 55 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 56 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 56 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 57 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 57 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 58 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 58 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 59 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 59 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 60 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 60 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 61 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 61 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 62 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 62 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix (1*((2^18)*1)) f416S4GramYInt ) 63 j)
      (fun (_ : Fin 1) (j : Fin 64) => ( f416rawS4Form) 63 j) (by decide +kernel)
    exact h 0 b

#print axioms f416_S4Gram_hF_rows_0
end TorusLean.BosonFiniteCertificate
