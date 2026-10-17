import torus.shared.BosonFiniteCertificateNatFourHS416HCompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f416_HCompression_hD_rows_0 (a : Fin 64) (hlo : 0 ≤ a.val) (hhi : a.val < 64) (b : Fin 10) :
    (natFourIntegerMatrix 180180 f416HCompressionCoordinates) a b=(b416relative) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 0 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 1 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 2 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 3 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 4 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 5 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 6 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 7 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 8 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 9 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 10 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 11 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 12 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 13 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 14 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 15 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 15 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 16 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 17 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 17 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 18 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 18 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 19 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 19 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 20 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 20 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 21 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 21 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 22 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 22 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 23 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 23 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 24 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 24 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 25 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 25 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 26 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 26 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 27 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 27 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 28 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 28 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 29 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 29 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 30 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 30 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 31 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 31 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 32 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 32 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 33 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 33 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 34 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 34 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 35 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 35 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 36 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 36 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 37 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 37 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 38 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 38 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 39 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 39 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 40 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 40 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 41 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 41 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 42 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 42 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 43 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 43 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 44 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 44 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 45 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 45 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 46 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 46 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 47 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 47 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 48 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 48 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 49 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 49 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 50 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 50 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 51 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 51 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 52 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 52 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 53 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 53 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 54 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 54 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 55 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 55 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 56 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 56 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 57 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 57 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 58 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 58 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 59 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 59 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 60 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 60 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 61 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 61 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 62 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 62 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416HCompressionCoordinates) 63 j)
      (fun (_ : Fin 1) (j : Fin 10) => (b416relative) 63 j) (by decide +kernel)
    exact h 0 b

#print axioms f416_HCompression_hD_rows_0
end TorusLean.BosonFiniteCertificate
