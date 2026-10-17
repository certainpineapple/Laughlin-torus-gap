import torus.shared.BosonFiniteCertificateNatFourHS416HCompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f416_HCompression_hM_rows_2 (a : Fin 64) (hlo : 32 ≤ a.val) (hhi : a.val < 48) (b : Fin 64) :
    (natFourIntegerMatrix 8 f416HCompressionInteger) a b=(f416rawHForm) a b := by
  fin_cases a
  · change 32 ≤ (0 : ℕ) at hlo
    omega
  · change 32 ≤ (1 : ℕ) at hlo
    omega
  · change 32 ≤ (2 : ℕ) at hlo
    omega
  · change 32 ≤ (3 : ℕ) at hlo
    omega
  · change 32 ≤ (4 : ℕ) at hlo
    omega
  · change 32 ≤ (5 : ℕ) at hlo
    omega
  · change 32 ≤ (6 : ℕ) at hlo
    omega
  · change 32 ≤ (7 : ℕ) at hlo
    omega
  · change 32 ≤ (8 : ℕ) at hlo
    omega
  · change 32 ≤ (9 : ℕ) at hlo
    omega
  · change 32 ≤ (10 : ℕ) at hlo
    omega
  · change 32 ≤ (11 : ℕ) at hlo
    omega
  · change 32 ≤ (12 : ℕ) at hlo
    omega
  · change 32 ≤ (13 : ℕ) at hlo
    omega
  · change 32 ≤ (14 : ℕ) at hlo
    omega
  · change 32 ≤ (15 : ℕ) at hlo
    omega
  · change 32 ≤ (16 : ℕ) at hlo
    omega
  · change 32 ≤ (17 : ℕ) at hlo
    omega
  · change 32 ≤ (18 : ℕ) at hlo
    omega
  · change 32 ≤ (19 : ℕ) at hlo
    omega
  · change 32 ≤ (20 : ℕ) at hlo
    omega
  · change 32 ≤ (21 : ℕ) at hlo
    omega
  · change 32 ≤ (22 : ℕ) at hlo
    omega
  · change 32 ≤ (23 : ℕ) at hlo
    omega
  · change 32 ≤ (24 : ℕ) at hlo
    omega
  · change 32 ≤ (25 : ℕ) at hlo
    omega
  · change 32 ≤ (26 : ℕ) at hlo
    omega
  · change 32 ≤ (27 : ℕ) at hlo
    omega
  · change 32 ≤ (28 : ℕ) at hlo
    omega
  · change 32 ≤ (29 : ℕ) at hlo
    omega
  · change 32 ≤ (30 : ℕ) at hlo
    omega
  · change 32 ≤ (31 : ℕ) at hlo
    omega
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 32 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 32 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 33 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 33 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 34 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 34 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 35 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 35 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 36 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 36 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 37 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 37 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 38 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 38 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 39 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 39 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 40 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 40 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 41 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 41 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 42 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 42 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 43 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 43 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 44 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 44 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 45 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 45 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 46 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 46 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 47 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 47 j) (by decide +kernel)
    exact h 0 b
  · change (48 : ℕ) < 48 at hhi
    omega
  · change (49 : ℕ) < 48 at hhi
    omega
  · change (50 : ℕ) < 48 at hhi
    omega
  · change (51 : ℕ) < 48 at hhi
    omega
  · change (52 : ℕ) < 48 at hhi
    omega
  · change (53 : ℕ) < 48 at hhi
    omega
  · change (54 : ℕ) < 48 at hhi
    omega
  · change (55 : ℕ) < 48 at hhi
    omega
  · change (56 : ℕ) < 48 at hhi
    omega
  · change (57 : ℕ) < 48 at hhi
    omega
  · change (58 : ℕ) < 48 at hhi
    omega
  · change (59 : ℕ) < 48 at hhi
    omega
  · change (60 : ℕ) < 48 at hhi
    omega
  · change (61 : ℕ) < 48 at hhi
    omega
  · change (62 : ℕ) < 48 at hhi
    omega
  · change (63 : ℕ) < 48 at hhi
    omega

#print axioms f416_HCompression_hM_rows_2
end TorusLean.BosonFiniteCertificate
