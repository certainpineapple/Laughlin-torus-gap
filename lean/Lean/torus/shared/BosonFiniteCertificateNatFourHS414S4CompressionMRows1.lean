import torus.shared.BosonFiniteCertificateNatFourHS414S4CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f414_S4Compression_hM_rows_1 (a : Fin 47) (hlo : 24 ≤ a.val) (hhi : a.val < 47) (b : Fin 47) :
    (natFourIntegerMatrix 4 f414S4CompressionInteger) a b=(f414rawS4Form) a b := by
  fin_cases a
  · change 24 ≤ (0 : ℕ) at hlo
    omega
  · change 24 ≤ (1 : ℕ) at hlo
    omega
  · change 24 ≤ (2 : ℕ) at hlo
    omega
  · change 24 ≤ (3 : ℕ) at hlo
    omega
  · change 24 ≤ (4 : ℕ) at hlo
    omega
  · change 24 ≤ (5 : ℕ) at hlo
    omega
  · change 24 ≤ (6 : ℕ) at hlo
    omega
  · change 24 ≤ (7 : ℕ) at hlo
    omega
  · change 24 ≤ (8 : ℕ) at hlo
    omega
  · change 24 ≤ (9 : ℕ) at hlo
    omega
  · change 24 ≤ (10 : ℕ) at hlo
    omega
  · change 24 ≤ (11 : ℕ) at hlo
    omega
  · change 24 ≤ (12 : ℕ) at hlo
    omega
  · change 24 ≤ (13 : ℕ) at hlo
    omega
  · change 24 ≤ (14 : ℕ) at hlo
    omega
  · change 24 ≤ (15 : ℕ) at hlo
    omega
  · change 24 ≤ (16 : ℕ) at hlo
    omega
  · change 24 ≤ (17 : ℕ) at hlo
    omega
  · change 24 ≤ (18 : ℕ) at hlo
    omega
  · change 24 ≤ (19 : ℕ) at hlo
    omega
  · change 24 ≤ (20 : ℕ) at hlo
    omega
  · change 24 ≤ (21 : ℕ) at hlo
    omega
  · change 24 ≤ (22 : ℕ) at hlo
    omega
  · change 24 ≤ (23 : ℕ) at hlo
    omega
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 24 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 24 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 25 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 25 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 26 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 26 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 27 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 27 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 28 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 28 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 29 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 29 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 30 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 30 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 31 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 31 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 32 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 32 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 33 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 33 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 34 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 34 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 35 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 35 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 36 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 36 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 37 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 37 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 38 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 38 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 39 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 39 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 40 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 40 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 41 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 41 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 42 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 42 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 43 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 43 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 44 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 44 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 45 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 45 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 46 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 46 j) (by decide +kernel)
    exact h 0 b

#print axioms f414_S4Compression_hM_rows_1
end TorusLean.BosonFiniteCertificate
