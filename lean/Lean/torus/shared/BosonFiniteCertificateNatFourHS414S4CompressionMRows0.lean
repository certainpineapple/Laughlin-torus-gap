import torus.shared.BosonFiniteCertificateNatFourHS414S4CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f414_S4Compression_hM_rows_0 (a : Fin 47) (hlo : 0 ≤ a.val) (hhi : a.val < 24) (b : Fin 47) :
    (natFourIntegerMatrix 4 f414S4CompressionInteger) a b=(f414rawS4Form) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 0 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 1 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 2 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 3 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 4 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 5 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 6 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 7 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 8 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 9 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 10 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 11 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 12 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 13 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 14 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 15 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 15 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 16 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 17 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 17 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 18 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 18 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 19 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 19 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 20 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 20 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 21 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 21 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 22 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 22 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414S4CompressionInteger) 23 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawS4Form) 23 j) (by decide +kernel)
    exact h 0 b
  · change (24 : ℕ) < 24 at hhi
    omega
  · change (25 : ℕ) < 24 at hhi
    omega
  · change (26 : ℕ) < 24 at hhi
    omega
  · change (27 : ℕ) < 24 at hhi
    omega
  · change (28 : ℕ) < 24 at hhi
    omega
  · change (29 : ℕ) < 24 at hhi
    omega
  · change (30 : ℕ) < 24 at hhi
    omega
  · change (31 : ℕ) < 24 at hhi
    omega
  · change (32 : ℕ) < 24 at hhi
    omega
  · change (33 : ℕ) < 24 at hhi
    omega
  · change (34 : ℕ) < 24 at hhi
    omega
  · change (35 : ℕ) < 24 at hhi
    omega
  · change (36 : ℕ) < 24 at hhi
    omega
  · change (37 : ℕ) < 24 at hhi
    omega
  · change (38 : ℕ) < 24 at hhi
    omega
  · change (39 : ℕ) < 24 at hhi
    omega
  · change (40 : ℕ) < 24 at hhi
    omega
  · change (41 : ℕ) < 24 at hhi
    omega
  · change (42 : ℕ) < 24 at hhi
    omega
  · change (43 : ℕ) < 24 at hhi
    omega
  · change (44 : ℕ) < 24 at hhi
    omega
  · change (45 : ℕ) < 24 at hhi
    omega
  · change (46 : ℕ) < 24 at hhi
    omega

#print axioms f414_S4Compression_hM_rows_0
end TorusLean.BosonFiniteCertificate
