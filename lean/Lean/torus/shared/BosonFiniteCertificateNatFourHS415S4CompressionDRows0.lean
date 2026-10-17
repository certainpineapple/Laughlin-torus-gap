import torus.shared.BosonFiniteCertificateNatFourHS415S4CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f415_S4Compression_hD_rows_0 (a : Fin 54) (hlo : 0 ≤ a.val) (hhi : a.val < 54) (b : Fin 7) :
    (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) a b=(b415relative) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 0 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 1 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 2 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 3 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 4 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 5 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 6 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 7 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 8 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 9 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 10 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 11 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 12 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 13 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 14 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 15 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 15 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 16 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 17 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 17 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 18 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 18 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 19 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 19 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 20 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 20 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 21 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 21 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 22 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 22 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 23 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 23 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 24 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 24 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 25 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 25 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 26 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 26 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 27 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 27 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 28 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 28 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 29 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 29 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 30 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 30 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 31 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 31 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 32 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 32 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 33 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 33 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 34 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 34 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 35 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 35 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 36 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 36 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 37 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 37 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 38 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 38 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 39 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 39 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 40 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 40 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 41 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 41 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 42 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 42 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 43 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 43 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 44 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 44 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 45 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 45 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 46 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 46 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 47 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 47 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 48 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 48 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 49 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 49 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 50 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 50 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 51 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 51 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 52 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 52 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415S4CompressionCoordinates) 53 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 53 j) (by decide +kernel)
    exact h 0 b

#print axioms f415_S4Compression_hD_rows_0
end TorusLean.BosonFiniteCertificate
