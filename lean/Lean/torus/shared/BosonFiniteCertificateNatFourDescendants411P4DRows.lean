import torus.shared.BosonFiniteCertificateNatFourDescendants411P4Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f411desc4_bounded_decode (a : Fin 54) (b : Fin 4) :
    (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) a b=(f411desc4) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 0 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 1 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 2 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 3 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 4 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 5 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 6 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 7 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 8 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 9 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 10 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 11 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 12 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 13 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 14 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 15 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 15 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 16 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 17 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 17 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 18 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 18 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 19 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 19 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 20 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 20 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 21 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 21 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 22 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 22 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 23 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 23 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 24 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 24 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 25 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 25 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 26 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 26 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 27 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 27 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 28 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 28 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 29 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 29 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 30 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 30 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 31 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 31 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 32 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 32 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 33 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 33 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 34 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 34 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 35 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 35 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 36 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 36 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 37 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 37 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 38 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 38 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 39 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 39 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 40 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 40 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 41 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 41 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 42 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 42 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 43 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 43 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 44 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 44 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 45 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 45 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 46 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 46 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 47 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 47 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 48 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 48 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 49 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 49 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 50 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 50 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 51 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 51 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 52 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 52 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc4IntegerCoordinatesShared) 53 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc4) 53 j) (by decide +kernel)
    exact h 0 b

#print axioms f411desc4_bounded_decode

end TorusLean.BosonFiniteCertificate
