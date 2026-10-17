import torus.shared.BosonFiniteCertificateNatFourDescendants416CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f416_DescCompression_hD_rows_0 (a : Fin 64) (hlo : 0 ≤ a.val) (hhi : a.val < 64) (b : Fin 10) :
    (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) a b=(f416desc0) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 0 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 1 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 2 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 3 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 4 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 5 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 6 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 7 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 8 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 9 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 10 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 11 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 12 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 13 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 14 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 15 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 15 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 16 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 17 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 17 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 18 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 18 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 19 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 19 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 20 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 20 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 21 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 21 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 22 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 22 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 23 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 23 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 24 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 24 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 25 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 25 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 26 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 26 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 27 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 27 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 28 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 28 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 29 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 29 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 30 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 30 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 31 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 31 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 32 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 32 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 33 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 33 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 34 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 34 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 35 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 35 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 36 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 36 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 37 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 37 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 38 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 38 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 39 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 39 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 40 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 40 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 41 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 41 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 42 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 42 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 43 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 43 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 44 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 44 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 45 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 45 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 46 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 46 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 47 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 47 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 48 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 48 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 49 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 49 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 50 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 50 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 51 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 51 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 52 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 52 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 53 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 53 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 54 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 54 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 55 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 55 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 56 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 56 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 57 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 57 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 58 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 58 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 59 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 59 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 60 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 60 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 61 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 61 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 62 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 62 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 10) => (natFourIntegerMatrix 180180 f416DescCompressionCoordinates) 63 j)
      (fun (_ : Fin 1) (j : Fin 10) => (f416desc0) 63 j) (by decide +kernel)
    exact h 0 b

#print axioms f416_DescCompression_hD_rows_0
end TorusLean.BosonFiniteCertificate
