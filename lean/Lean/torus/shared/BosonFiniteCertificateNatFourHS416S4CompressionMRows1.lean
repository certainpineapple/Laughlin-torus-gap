import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f416_S4Compression_hM_rows_1 (a : Fin 64) (hlo : 16 ≤ a.val) (hhi : a.val < 32) (b : Fin 64) :
    (natFourIntegerMatrix 4 f416S4CompressionInteger) a b=(f416rawS4Form) a b := by
  fin_cases a
  · change 16 ≤ (0 : ℕ) at hlo
    omega
  · change 16 ≤ (1 : ℕ) at hlo
    omega
  · change 16 ≤ (2 : ℕ) at hlo
    omega
  · change 16 ≤ (3 : ℕ) at hlo
    omega
  · change 16 ≤ (4 : ℕ) at hlo
    omega
  · change 16 ≤ (5 : ℕ) at hlo
    omega
  · change 16 ≤ (6 : ℕ) at hlo
    omega
  · change 16 ≤ (7 : ℕ) at hlo
    omega
  · change 16 ≤ (8 : ℕ) at hlo
    omega
  · change 16 ≤ (9 : ℕ) at hlo
    omega
  · change 16 ≤ (10 : ℕ) at hlo
    omega
  · change 16 ≤ (11 : ℕ) at hlo
    omega
  · change 16 ≤ (12 : ℕ) at hlo
    omega
  · change 16 ≤ (13 : ℕ) at hlo
    omega
  · change 16 ≤ (14 : ℕ) at hlo
    omega
  · change 16 ≤ (15 : ℕ) at hlo
    omega
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 16 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 17 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 17 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 18 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 18 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 19 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 19 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 20 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 20 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 21 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 21 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 22 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 22 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 23 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 23 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 24 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 24 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 25 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 25 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 26 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 26 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 27 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 27 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 28 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 28 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 29 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 29 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 30 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 30 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 31 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 31 j) (by decide +kernel)
    exact h 0 b
  · change (32 : ℕ) < 32 at hhi
    omega
  · change (33 : ℕ) < 32 at hhi
    omega
  · change (34 : ℕ) < 32 at hhi
    omega
  · change (35 : ℕ) < 32 at hhi
    omega
  · change (36 : ℕ) < 32 at hhi
    omega
  · change (37 : ℕ) < 32 at hhi
    omega
  · change (38 : ℕ) < 32 at hhi
    omega
  · change (39 : ℕ) < 32 at hhi
    omega
  · change (40 : ℕ) < 32 at hhi
    omega
  · change (41 : ℕ) < 32 at hhi
    omega
  · change (42 : ℕ) < 32 at hhi
    omega
  · change (43 : ℕ) < 32 at hhi
    omega
  · change (44 : ℕ) < 32 at hhi
    omega
  · change (45 : ℕ) < 32 at hhi
    omega
  · change (46 : ℕ) < 32 at hhi
    omega
  · change (47 : ℕ) < 32 at hhi
    omega
  · change (48 : ℕ) < 32 at hhi
    omega
  · change (49 : ℕ) < 32 at hhi
    omega
  · change (50 : ℕ) < 32 at hhi
    omega
  · change (51 : ℕ) < 32 at hhi
    omega
  · change (52 : ℕ) < 32 at hhi
    omega
  · change (53 : ℕ) < 32 at hhi
    omega
  · change (54 : ℕ) < 32 at hhi
    omega
  · change (55 : ℕ) < 32 at hhi
    omega
  · change (56 : ℕ) < 32 at hhi
    omega
  · change (57 : ℕ) < 32 at hhi
    omega
  · change (58 : ℕ) < 32 at hhi
    omega
  · change (59 : ℕ) < 32 at hhi
    omega
  · change (60 : ℕ) < 32 at hhi
    omega
  · change (61 : ℕ) < 32 at hhi
    omega
  · change (62 : ℕ) < 32 at hhi
    omega
  · change (63 : ℕ) < 32 at hhi
    omega

#print axioms f416_S4Compression_hM_rows_1
end TorusLean.BosonFiniteCertificate
