import torus.shared.BosonFiniteCertificateNatFourDescendants411P5Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f411desc5_bounded_decode (a : Fin 64) (b : Fin 4) :
    (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) a b=(f411desc5) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 0 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 1 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 2 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 3 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 4 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 5 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 6 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 7 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 8 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 9 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 10 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 11 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 12 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 13 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 14 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 15 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 15 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 16 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 17 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 17 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 18 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 18 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 19 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 19 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 20 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 20 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 21 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 21 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 22 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 22 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 23 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 23 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 24 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 24 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 25 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 25 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 26 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 26 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 27 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 27 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 28 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 28 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 29 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 29 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 30 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 30 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 31 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 31 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 32 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 32 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 33 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 33 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 34 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 34 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 35 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 35 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 36 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 36 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 37 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 37 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 38 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 38 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 39 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 39 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 40 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 40 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 41 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 41 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 42 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 42 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 43 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 43 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 44 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 44 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 45 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 45 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 46 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 46 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 47 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 47 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 48 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 48 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 49 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 49 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 50 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 50 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 51 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 51 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 52 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 52 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 53 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 53 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 54 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 54 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 55 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 55 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 56 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 56 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 57 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 57 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 58 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 58 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 59 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 59 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 60 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 60 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 61 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 61 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 62 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 62 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc5IntegerCoordinatesShared) 63 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc5) 63 j) (by decide +kernel)
    exact h 0 b

#print axioms f411desc5_bounded_decode

end TorusLean.BosonFiniteCertificate
