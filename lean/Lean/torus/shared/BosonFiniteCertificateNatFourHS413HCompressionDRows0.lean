import torus.shared.BosonFiniteCertificateNatFourHS413HCompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413_HCompression_hD_rows_0 (a : Fin 39) (hlo : 0 ≤ a.val) (hhi : a.val < 39) (b : Fin 5) :
    (natFourIntegerMatrix 27720 f413HCompressionCoordinates) a b=(b413relative) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 0 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 1 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 2 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 3 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 4 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 5 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 6 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 7 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 8 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 9 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 10 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 11 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 12 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 13 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 14 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 15 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 15 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 16 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 17 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 17 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 18 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 18 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 19 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 19 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 20 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 20 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 21 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 21 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 22 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 22 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 23 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 23 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 24 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 24 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 25 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 25 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 26 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 26 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 27 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 27 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 28 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 28 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 29 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 29 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 30 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 30 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 31 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 31 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 32 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 32 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 33 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 33 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 34 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 34 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 35 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 35 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 36 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 36 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 37 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 37 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413HCompressionCoordinates) 38 j)
      (fun (_ : Fin 1) (j : Fin 5) => (b413relative) 38 j) (by decide +kernel)
    exact h 0 b

#print axioms f413_HCompression_hD_rows_0
end TorusLean.BosonFiniteCertificate
