import torus.shared.BosonFiniteCertificateNatFourHS414HCompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f414_HCompression_hD_rows_0 (a : Fin 47) (hlo : 0 ≤ a.val) (hhi : a.val < 47) (b : Fin 8) :
    (natFourIntegerMatrix 180180 f414HCompressionCoordinates) a b=(b414relative) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 0 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 1 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 2 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 3 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 4 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 5 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 6 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 7 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 8 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 9 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 10 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 11 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 12 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 13 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 14 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 15 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 15 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 16 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 17 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 17 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 18 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 18 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 19 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 19 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 20 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 20 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 21 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 21 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 22 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 22 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 23 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 23 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 24 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 24 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 25 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 25 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 26 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 26 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 27 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 27 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 28 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 28 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 29 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 29 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 30 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 30 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 31 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 31 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 32 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 32 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 33 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 33 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 34 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 34 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 35 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 35 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 36 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 36 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 37 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 37 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 38 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 38 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 39 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 39 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 40 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 40 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 41 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 41 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 42 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 42 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 43 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 43 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 44 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 44 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 45 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 45 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 8) => (natFourIntegerMatrix 180180 f414HCompressionCoordinates) 46 j)
      (fun (_ : Fin 1) (j : Fin 8) => (b414relative) 46 j) (by decide +kernel)
    exact h 0 b

#print axioms f414_HCompression_hD_rows_0
end TorusLean.BosonFiniteCertificate
