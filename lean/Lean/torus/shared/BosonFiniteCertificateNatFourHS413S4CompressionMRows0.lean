import torus.shared.BosonFiniteCertificateNatFourHS413S4CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413_S4Compression_hM_rows_0 (a : Fin 39) (hlo : 0 ≤ a.val) (hhi : a.val < 39) (b : Fin 39) :
    (natFourIntegerMatrix 4 f413S4CompressionInteger) a b=(f413rawS4Form) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 0 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 1 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 2 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 3 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 4 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 5 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 6 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 7 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 8 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 9 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 10 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 11 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 12 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 13 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 14 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 15 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 15 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 16 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 17 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 17 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 18 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 18 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 19 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 19 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 20 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 20 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 21 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 21 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 22 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 22 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 23 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 23 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 24 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 24 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 25 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 25 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 26 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 26 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 27 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 27 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 28 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 28 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 29 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 29 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 30 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 30 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 31 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 31 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 32 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 32 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 33 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 33 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 34 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 34 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 35 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 35 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 36 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 36 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 37 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 37 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 4 f413S4CompressionInteger) 38 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawS4Form) 38 j) (by decide +kernel)
    exact h 0 b

#print axioms f413_S4Compression_hM_rows_0
end TorusLean.BosonFiniteCertificate
