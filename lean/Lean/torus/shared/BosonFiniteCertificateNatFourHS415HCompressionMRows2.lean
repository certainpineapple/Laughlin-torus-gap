import torus.shared.BosonFiniteCertificateNatFourHS415HCompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f415_HCompression_hM_rows_2 (a : Fin 54) (hlo : 36 ≤ a.val) (hhi : a.val < 54) (b : Fin 54) :
    (natFourIntegerMatrix 4 f415HCompressionInteger) a b=(f415rawHForm) a b := by
  fin_cases a
  · change 36 ≤ (0 : ℕ) at hlo
    omega
  · change 36 ≤ (1 : ℕ) at hlo
    omega
  · change 36 ≤ (2 : ℕ) at hlo
    omega
  · change 36 ≤ (3 : ℕ) at hlo
    omega
  · change 36 ≤ (4 : ℕ) at hlo
    omega
  · change 36 ≤ (5 : ℕ) at hlo
    omega
  · change 36 ≤ (6 : ℕ) at hlo
    omega
  · change 36 ≤ (7 : ℕ) at hlo
    omega
  · change 36 ≤ (8 : ℕ) at hlo
    omega
  · change 36 ≤ (9 : ℕ) at hlo
    omega
  · change 36 ≤ (10 : ℕ) at hlo
    omega
  · change 36 ≤ (11 : ℕ) at hlo
    omega
  · change 36 ≤ (12 : ℕ) at hlo
    omega
  · change 36 ≤ (13 : ℕ) at hlo
    omega
  · change 36 ≤ (14 : ℕ) at hlo
    omega
  · change 36 ≤ (15 : ℕ) at hlo
    omega
  · change 36 ≤ (16 : ℕ) at hlo
    omega
  · change 36 ≤ (17 : ℕ) at hlo
    omega
  · change 36 ≤ (18 : ℕ) at hlo
    omega
  · change 36 ≤ (19 : ℕ) at hlo
    omega
  · change 36 ≤ (20 : ℕ) at hlo
    omega
  · change 36 ≤ (21 : ℕ) at hlo
    omega
  · change 36 ≤ (22 : ℕ) at hlo
    omega
  · change 36 ≤ (23 : ℕ) at hlo
    omega
  · change 36 ≤ (24 : ℕ) at hlo
    omega
  · change 36 ≤ (25 : ℕ) at hlo
    omega
  · change 36 ≤ (26 : ℕ) at hlo
    omega
  · change 36 ≤ (27 : ℕ) at hlo
    omega
  · change 36 ≤ (28 : ℕ) at hlo
    omega
  · change 36 ≤ (29 : ℕ) at hlo
    omega
  · change 36 ≤ (30 : ℕ) at hlo
    omega
  · change 36 ≤ (31 : ℕ) at hlo
    omega
  · change 36 ≤ (32 : ℕ) at hlo
    omega
  · change 36 ≤ (33 : ℕ) at hlo
    omega
  · change 36 ≤ (34 : ℕ) at hlo
    omega
  · change 36 ≤ (35 : ℕ) at hlo
    omega
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 36 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 36 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 37 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 37 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 38 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 38 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 39 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 39 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 40 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 40 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 41 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 41 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 42 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 42 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 43 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 43 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 44 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 44 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 45 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 45 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 46 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 46 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 47 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 47 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 48 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 48 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 49 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 49 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 50 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 50 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 51 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 51 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 52 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 52 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 53 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 53 j) (by decide +kernel)
    exact h 0 b

#print axioms f415_HCompression_hM_rows_2
end TorusLean.BosonFiniteCertificate
