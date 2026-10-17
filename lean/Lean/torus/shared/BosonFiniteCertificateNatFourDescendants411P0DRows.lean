import torus.shared.BosonFiniteCertificateNatFourDescendants411P0Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f411desc0_bounded_decode (a : Fin 27) (b : Fin 4) :
    (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) a b=(f411desc0) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 0 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 1 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 2 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 3 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 4 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 5 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 6 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 7 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 8 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 9 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 10 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 11 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 12 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 13 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 14 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 15 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 15 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 16 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 17 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 17 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 18 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 18 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 19 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 19 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 20 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 20 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 21 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 21 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 22 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 22 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 23 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 23 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 24 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 24 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 25 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 25 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 4) => (natFourIntegerMatrix 2520 f411desc0IntegerCoordinatesShared) 26 j)
      (fun (_ : Fin 1) (j : Fin 4) => (f411desc0) 26 j) (by decide +kernel)
    exact h 0 b

#print axioms f411desc0_bounded_decode

end TorusLean.BosonFiniteCertificate
