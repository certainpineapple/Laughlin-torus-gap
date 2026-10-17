import torus.shared.BosonFiniteCertificateNatFourHS416HCompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f416_HCompression_hM_rows_1 (a : Fin 64) (hlo : 16 ≤ a.val) (hhi : a.val < 32) (b : Fin 64) :
    (natFourIntegerMatrix 8 f416HCompressionInteger) a b=(f416rawHForm) a b := by
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
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 16 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 17 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 17 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 18 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 18 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 19 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 19 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 20 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 20 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 21 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 21 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 22 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 22 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 23 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 23 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 24 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 24 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 25 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 25 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 26 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 26 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 27 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 27 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 28 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 28 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 29 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 29 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 30 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 30 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 31 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 31 j) (by decide +kernel)
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

#print axioms f416_HCompression_hM_rows_1
end TorusLean.BosonFiniteCertificate
