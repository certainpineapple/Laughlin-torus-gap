import torus.shared.BosonFiniteCertificateNatFourHS416S4CompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f416_S4Compression_hM_rows_0 (a : Fin 64) (hlo : 0 ≤ a.val) (hhi : a.val < 16) (b : Fin 64) :
    (natFourIntegerMatrix 4 f416S4CompressionInteger) a b=(f416rawS4Form) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 0 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 1 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 2 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 3 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 4 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 5 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 6 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 7 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 8 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 9 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 10 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 11 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 12 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 13 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 14 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 4 f416S4CompressionInteger) 15 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawS4Form) 15 j) (by decide +kernel)
    exact h 0 b
  · change (16 : ℕ) < 16 at hhi
    omega
  · change (17 : ℕ) < 16 at hhi
    omega
  · change (18 : ℕ) < 16 at hhi
    omega
  · change (19 : ℕ) < 16 at hhi
    omega
  · change (20 : ℕ) < 16 at hhi
    omega
  · change (21 : ℕ) < 16 at hhi
    omega
  · change (22 : ℕ) < 16 at hhi
    omega
  · change (23 : ℕ) < 16 at hhi
    omega
  · change (24 : ℕ) < 16 at hhi
    omega
  · change (25 : ℕ) < 16 at hhi
    omega
  · change (26 : ℕ) < 16 at hhi
    omega
  · change (27 : ℕ) < 16 at hhi
    omega
  · change (28 : ℕ) < 16 at hhi
    omega
  · change (29 : ℕ) < 16 at hhi
    omega
  · change (30 : ℕ) < 16 at hhi
    omega
  · change (31 : ℕ) < 16 at hhi
    omega
  · change (32 : ℕ) < 16 at hhi
    omega
  · change (33 : ℕ) < 16 at hhi
    omega
  · change (34 : ℕ) < 16 at hhi
    omega
  · change (35 : ℕ) < 16 at hhi
    omega
  · change (36 : ℕ) < 16 at hhi
    omega
  · change (37 : ℕ) < 16 at hhi
    omega
  · change (38 : ℕ) < 16 at hhi
    omega
  · change (39 : ℕ) < 16 at hhi
    omega
  · change (40 : ℕ) < 16 at hhi
    omega
  · change (41 : ℕ) < 16 at hhi
    omega
  · change (42 : ℕ) < 16 at hhi
    omega
  · change (43 : ℕ) < 16 at hhi
    omega
  · change (44 : ℕ) < 16 at hhi
    omega
  · change (45 : ℕ) < 16 at hhi
    omega
  · change (46 : ℕ) < 16 at hhi
    omega
  · change (47 : ℕ) < 16 at hhi
    omega
  · change (48 : ℕ) < 16 at hhi
    omega
  · change (49 : ℕ) < 16 at hhi
    omega
  · change (50 : ℕ) < 16 at hhi
    omega
  · change (51 : ℕ) < 16 at hhi
    omega
  · change (52 : ℕ) < 16 at hhi
    omega
  · change (53 : ℕ) < 16 at hhi
    omega
  · change (54 : ℕ) < 16 at hhi
    omega
  · change (55 : ℕ) < 16 at hhi
    omega
  · change (56 : ℕ) < 16 at hhi
    omega
  · change (57 : ℕ) < 16 at hhi
    omega
  · change (58 : ℕ) < 16 at hhi
    omega
  · change (59 : ℕ) < 16 at hhi
    omega
  · change (60 : ℕ) < 16 at hhi
    omega
  · change (61 : ℕ) < 16 at hhi
    omega
  · change (62 : ℕ) < 16 at hhi
    omega
  · change (63 : ℕ) < 16 at hhi
    omega

#print axioms f416_S4Compression_hM_rows_0
end TorusLean.BosonFiniteCertificate
