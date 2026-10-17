import torus.shared.BosonFiniteCertificateNatFourDescendants413P1Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413desc1_bounded_decode (a : Fin 47) (b : Fin 5) :
    (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) a b=(f413desc1) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 0 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 1 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 2 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 3 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 4 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 5 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 6 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 7 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 8 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 9 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 10 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 11 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 12 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 13 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 14 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 15 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 15 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 16 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 17 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 17 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 18 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 18 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 19 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 19 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 20 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 20 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 21 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 21 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 22 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 22 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 23 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 23 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 24 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 24 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 25 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 25 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 26 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 26 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 27 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 27 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 28 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 28 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 29 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 29 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 30 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 30 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 31 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 31 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 32 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 32 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 33 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 33 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 34 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 34 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 35 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 35 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 36 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 36 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 37 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 37 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 38 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 38 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 39 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 39 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 40 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 40 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 41 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 41 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 42 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 42 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 43 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 43 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 44 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 44 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 45 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 45 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc1IntegerCoordinatesShared) 46 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc1) 46 j) (by decide +kernel)
    exact h 0 b

#print axioms f413desc1_bounded_decode

end TorusLean.BosonFiniteCertificate
