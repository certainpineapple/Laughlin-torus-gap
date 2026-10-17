import torus.shared.BosonFiniteCertificateNatFourHS413HCompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413_HCompression_hM_rows_0 (a : Fin 39) (hlo : 0 ≤ a.val) (hhi : a.val < 39) (b : Fin 39) :
    (natFourIntegerMatrix 2 f413HCompressionInteger) a b=(f413rawHForm) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 0 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 1 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 2 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 3 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 4 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 5 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 6 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 7 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 8 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 9 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 10 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 11 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 12 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 13 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 14 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 15 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 15 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 16 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 17 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 17 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 18 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 18 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 19 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 19 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 20 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 20 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 21 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 21 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 22 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 22 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 23 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 23 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 24 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 24 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 25 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 25 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 26 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 26 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 27 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 27 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 28 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 28 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 29 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 29 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 30 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 30 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 31 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 31 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 32 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 32 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 33 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 33 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 34 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 34 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 35 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 35 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 36 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 36 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 37 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 37 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 39) => (natFourIntegerMatrix 2 f413HCompressionInteger) 38 j)
      (fun (_ : Fin 1) (j : Fin 39) => (f413rawHForm) 38 j) (by decide +kernel)
    exact h 0 b

#print axioms f413_HCompression_hM_rows_0
end TorusLean.BosonFiniteCertificate
