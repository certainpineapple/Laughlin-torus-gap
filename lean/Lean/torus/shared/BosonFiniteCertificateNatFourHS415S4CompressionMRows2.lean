import torus.shared.BosonFiniteCertificateNatFourHS415S4CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f415_S4Compression_hM_rows_2 (a : Fin 54) (hlo : 36 ≤ a.val) (hhi : a.val < 54) (b : Fin 54) :
    (natFourIntegerMatrix 2 f415S4CompressionInteger) a b=(f415rawS4Form) a b := by
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
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 2 f415S4CompressionInteger) 36 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawS4Form) 36 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 2 f415S4CompressionInteger) 37 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawS4Form) 37 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 2 f415S4CompressionInteger) 38 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawS4Form) 38 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 2 f415S4CompressionInteger) 39 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawS4Form) 39 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 2 f415S4CompressionInteger) 40 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawS4Form) 40 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 2 f415S4CompressionInteger) 41 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawS4Form) 41 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 2 f415S4CompressionInteger) 42 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawS4Form) 42 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 2 f415S4CompressionInteger) 43 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawS4Form) 43 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 2 f415S4CompressionInteger) 44 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawS4Form) 44 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 2 f415S4CompressionInteger) 45 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawS4Form) 45 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 2 f415S4CompressionInteger) 46 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawS4Form) 46 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 2 f415S4CompressionInteger) 47 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawS4Form) 47 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 2 f415S4CompressionInteger) 48 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawS4Form) 48 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 2 f415S4CompressionInteger) 49 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawS4Form) 49 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 2 f415S4CompressionInteger) 50 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawS4Form) 50 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 2 f415S4CompressionInteger) 51 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawS4Form) 51 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 2 f415S4CompressionInteger) 52 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawS4Form) 52 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 2 f415S4CompressionInteger) 53 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawS4Form) 53 j) (by decide +kernel)
    exact h 0 b

#print axioms f415_S4Compression_hM_rows_2
end TorusLean.BosonFiniteCertificate
