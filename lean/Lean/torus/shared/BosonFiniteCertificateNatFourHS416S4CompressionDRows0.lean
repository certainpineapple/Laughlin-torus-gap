import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f416_S4Compression_hD_rows_0 (a : Fin 64) (hlo : 0 ≤ a.val) (hhi : a.val < 64) (b : Fin 10) :
    (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) a b=(b416relative) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 0 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 1 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 2 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 3 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 4 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 5 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 6 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 7 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 8 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 9 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 10 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 11 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 12 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 13 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 14 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 15 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 15 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 16 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 17 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 17 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 18 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 18 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 19 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 19 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 20 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 20 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 21 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 21 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 22 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 22 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 23 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 23 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 24 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 24 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 25 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 25 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 26 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 26 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 27 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 27 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 28 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 28 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 29 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 29 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 30 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 30 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 31 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 31 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 32 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 32 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 33 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 33 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 34 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 34 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 35 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 35 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 36 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 36 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 37 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 37 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 38 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 38 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 39 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 39 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 40 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 40 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 41 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 41 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 42 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 42 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 43 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 43 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 44 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 44 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 45 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 45 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 46 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 46 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 47 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 47 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 48 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 48 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 49 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 49 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 50 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 50 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 51 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 51 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 52 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 52 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 53 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 53 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 54 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 54 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 55 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 55 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 56 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 56 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 57 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 57 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 58 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 58 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 59 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 59 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 60 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 60 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 61 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 61 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 62 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 62 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416S4CompressionCoordinates) 63 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 63 j) (by decide +kernel)
    exact h 0 b

#print axioms f416_S4Compression_hD_rows_0
end TorusLean.BosonFiniteCertificate
