import torus.shared.BosonFiniteCertificateNatFourHS415HCompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f415_HCompression_hD_rows_0 (a : Fin 54) (hlo : 0 ≤ a.val) (hhi : a.val < 54) (b : Fin 7) :
    (natFourIntegerMatrix 360360 f415HCompressionCoordinates) a b=(b415relative) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 0 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 1 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 2 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 3 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 4 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 5 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 6 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 7 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 8 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 9 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 10 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 11 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 12 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 13 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 14 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 15 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 15 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 16 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 17 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 17 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 18 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 18 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 19 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 19 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 20 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 20 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 21 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 21 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 22 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 22 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 23 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 23 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 24 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 24 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 25 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 25 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 26 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 26 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 27 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 27 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 28 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 28 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 29 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 29 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 30 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 30 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 31 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 31 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 32 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 32 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 33 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 33 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 34 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 34 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 35 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 35 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 36 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 36 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 37 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 37 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 38 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 38 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 39 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 39 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 40 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 40 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 41 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 41 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 42 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 42 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 43 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 43 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 44 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 44 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 45 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 45 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 46 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 46 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 47 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 47 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 48 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 48 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 49 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 49 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 50 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 50 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 51 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 51 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 52 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 52 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415HCompressionCoordinates) 53 j)
      (fun (_ : Fin 1) (j : Fin 7) => (b415relative) 53 j) (by decide +kernel)
    exact h 0 b

#print axioms f415_HCompression_hD_rows_0
end TorusLean.BosonFiniteCertificate
