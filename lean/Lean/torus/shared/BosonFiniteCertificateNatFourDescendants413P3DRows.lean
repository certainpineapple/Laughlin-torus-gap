import torus.shared.BosonFiniteCertificateNatFourDescendants413P3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413desc3_bounded_decode (a : Fin 64) (b : Fin 5) :
    (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) a b=(f413desc3) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 0 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 1 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 2 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 3 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 4 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 5 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 6 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 7 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 8 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 9 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 10 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 11 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 12 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 13 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 14 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 15 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 15 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 16 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 17 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 17 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 18 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 18 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 19 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 19 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 20 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 20 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 21 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 21 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 22 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 22 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 23 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 23 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 24 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 24 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 25 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 25 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 26 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 26 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 27 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 27 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 28 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 28 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 29 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 29 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 30 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 30 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 31 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 31 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 32 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 32 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 33 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 33 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 34 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 34 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 35 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 35 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 36 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 36 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 37 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 37 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 38 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 38 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 39 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 39 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 40 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 40 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 41 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 41 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 42 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 42 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 43 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 43 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 44 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 44 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 45 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 45 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 46 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 46 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 47 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 47 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 48 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 48 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 49 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 49 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 50 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 50 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 51 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 51 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 52 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 52 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 53 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 53 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 54 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 54 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 55 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 55 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 56 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 56 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 57 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 57 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 58 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 58 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 59 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 59 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 60 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 60 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 61 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 61 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 62 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 62 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 5) => (natFourIntegerMatrix 27720 f413desc3IntegerCoordinatesShared) 63 j)
      (fun (_ : Fin 1) (j : Fin 5) => (f413desc3) 63 j) (by decide +kernel)
    exact h 0 b

#print axioms f413desc3_bounded_decode

end TorusLean.BosonFiniteCertificate
