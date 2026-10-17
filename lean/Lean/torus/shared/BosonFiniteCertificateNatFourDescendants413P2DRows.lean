import torus.shared.BosonFiniteCertificateNatFourDescendants413P2Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413desc2_bounded_decode (a : Fin 54) (b : Fin 5) :
    (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) a b=(f413desc2) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 0 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 1 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 2 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 3 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 4 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 5 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 6 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 7 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 8 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 9 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 10 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 11 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 12 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 13 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 14 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 15 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 15 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 16 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 17 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 17 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 18 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 18 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 19 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 19 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 20 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 20 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 21 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 21 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 22 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 22 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 23 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 23 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 24 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 24 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 25 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 25 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 26 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 26 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 27 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 27 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 28 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 28 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 29 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 29 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 30 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 30 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 31 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 31 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 32 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 32 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 33 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 33 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 34 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 34 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 35 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 35 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 36 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 36 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 37 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 37 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 38 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 38 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 39 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 39 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 40 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 40 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 41 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 41 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 42 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 42 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 43 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 43 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 44 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 44 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 45 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 45 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 46 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 46 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 47 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 47 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 48 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 48 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 49 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 49 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 50 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 50 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 51 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 51 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 52 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 52 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc2IntegerCoordinatesShared) 53 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc2) 53 j) (by decide +kernel)
    exact h 0 b

#print axioms f413desc2_bounded_decode

end TorusLean.BosonFiniteCertificate
