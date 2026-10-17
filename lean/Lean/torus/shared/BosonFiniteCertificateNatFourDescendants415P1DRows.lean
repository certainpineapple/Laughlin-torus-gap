import torus.shared.BosonFiniteCertificateNatFourDescendants415P1Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f415desc1_bounded_decode (a : Fin 64) (b : Fin 7) :
    (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) a b=(f415desc1) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 0 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 1 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 2 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 3 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 4 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 5 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 6 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 7 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 8 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 9 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 10 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 11 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 12 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 13 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 14 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 15 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 15 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 16 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 17 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 17 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 18 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 18 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 19 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 19 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 20 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 20 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 21 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 21 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 22 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 22 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 23 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 23 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 24 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 24 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 25 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 25 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 26 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 26 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 27 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 27 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 28 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 28 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 29 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 29 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 30 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 30 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 31 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 31 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 32 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 32 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 33 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 33 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 34 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 34 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 35 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 35 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 36 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 36 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 37 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 37 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 38 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 38 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 39 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 39 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 40 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 40 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 41 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 41 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 42 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 42 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 43 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 43 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 44 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 44 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 45 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 45 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 46 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 46 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 47 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 47 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 48 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 48 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 49 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 49 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 50 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 50 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 51 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 51 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 52 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 52 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 53 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 53 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 54 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 54 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 55 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 55 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 56 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 56 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 57 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 57 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 58 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 58 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 59 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 59 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 60 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 60 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 61 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 61 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 62 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 62 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 7) => (natFourIntegerMatrix 360360 f415desc1IntegerCoordinatesShared) 63 j)
      (fun (_ : Fin 1) (j : Fin 7) => (f415desc1) 63 j) (by decide +kernel)
    exact h 0 b

#print axioms f415desc1_bounded_decode

end TorusLean.BosonFiniteCertificate
