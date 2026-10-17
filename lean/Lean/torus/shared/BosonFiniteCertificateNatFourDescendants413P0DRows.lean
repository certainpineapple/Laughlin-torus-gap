import torus.shared.BosonFiniteCertificateNatFourDescendants413P0Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413desc0_bounded_decode (a : Fin 39) (b : Fin 5) :
    (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) a b=(f413desc0) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 0 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 1 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 2 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 3 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 4 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 5 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 6 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 7 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 8 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 9 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 10 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 11 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 12 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 13 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 14 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 15 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 15 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 16 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 17 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 17 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 18 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 18 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 19 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 19 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 20 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 20 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 21 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 21 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 22 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 22 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 23 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 23 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 24 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 24 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 25 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 25 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 26 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 26 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 27 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 27 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 28 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 28 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 29 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 29 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 30 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 30 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 31 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 31 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 32 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 32 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 33 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 33 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 34 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 34 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 35 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 35 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 36 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 36 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 37 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 37 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc0IntegerCoordinatesShared) 38 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc0) 38 j) (by decide +kernel)
    exact h 0 b

#print axioms f413desc0_bounded_decode

end TorusLean.BosonFiniteCertificate
