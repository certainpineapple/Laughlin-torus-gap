import torus.shared.BosonFiniteCertificateNatFourHS416HCompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f416_HCompression_hM_rows_3 (a : Fin 64) (hlo : 48 ≤ a.val) (hhi : a.val < 64) (b : Fin 64) :
    (natFourIntegerMatrix 8 f416HCompressionInteger) a b=(f416rawHForm) a b := by
  fin_cases a
  · change 48 ≤ (0 : ℕ) at hlo
    omega
  · change 48 ≤ (1 : ℕ) at hlo
    omega
  · change 48 ≤ (2 : ℕ) at hlo
    omega
  · change 48 ≤ (3 : ℕ) at hlo
    omega
  · change 48 ≤ (4 : ℕ) at hlo
    omega
  · change 48 ≤ (5 : ℕ) at hlo
    omega
  · change 48 ≤ (6 : ℕ) at hlo
    omega
  · change 48 ≤ (7 : ℕ) at hlo
    omega
  · change 48 ≤ (8 : ℕ) at hlo
    omega
  · change 48 ≤ (9 : ℕ) at hlo
    omega
  · change 48 ≤ (10 : ℕ) at hlo
    omega
  · change 48 ≤ (11 : ℕ) at hlo
    omega
  · change 48 ≤ (12 : ℕ) at hlo
    omega
  · change 48 ≤ (13 : ℕ) at hlo
    omega
  · change 48 ≤ (14 : ℕ) at hlo
    omega
  · change 48 ≤ (15 : ℕ) at hlo
    omega
  · change 48 ≤ (16 : ℕ) at hlo
    omega
  · change 48 ≤ (17 : ℕ) at hlo
    omega
  · change 48 ≤ (18 : ℕ) at hlo
    omega
  · change 48 ≤ (19 : ℕ) at hlo
    omega
  · change 48 ≤ (20 : ℕ) at hlo
    omega
  · change 48 ≤ (21 : ℕ) at hlo
    omega
  · change 48 ≤ (22 : ℕ) at hlo
    omega
  · change 48 ≤ (23 : ℕ) at hlo
    omega
  · change 48 ≤ (24 : ℕ) at hlo
    omega
  · change 48 ≤ (25 : ℕ) at hlo
    omega
  · change 48 ≤ (26 : ℕ) at hlo
    omega
  · change 48 ≤ (27 : ℕ) at hlo
    omega
  · change 48 ≤ (28 : ℕ) at hlo
    omega
  · change 48 ≤ (29 : ℕ) at hlo
    omega
  · change 48 ≤ (30 : ℕ) at hlo
    omega
  · change 48 ≤ (31 : ℕ) at hlo
    omega
  · change 48 ≤ (32 : ℕ) at hlo
    omega
  · change 48 ≤ (33 : ℕ) at hlo
    omega
  · change 48 ≤ (34 : ℕ) at hlo
    omega
  · change 48 ≤ (35 : ℕ) at hlo
    omega
  · change 48 ≤ (36 : ℕ) at hlo
    omega
  · change 48 ≤ (37 : ℕ) at hlo
    omega
  · change 48 ≤ (38 : ℕ) at hlo
    omega
  · change 48 ≤ (39 : ℕ) at hlo
    omega
  · change 48 ≤ (40 : ℕ) at hlo
    omega
  · change 48 ≤ (41 : ℕ) at hlo
    omega
  · change 48 ≤ (42 : ℕ) at hlo
    omega
  · change 48 ≤ (43 : ℕ) at hlo
    omega
  · change 48 ≤ (44 : ℕ) at hlo
    omega
  · change 48 ≤ (45 : ℕ) at hlo
    omega
  · change 48 ≤ (46 : ℕ) at hlo
    omega
  · change 48 ≤ (47 : ℕ) at hlo
    omega
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 48 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 48 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 49 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 49 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 50 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 50 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 51 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 51 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 52 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 52 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 53 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 53 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 54 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 54 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 55 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 55 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 56 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 56 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 57 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 57 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 58 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 58 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 59 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 59 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 60 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 60 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 61 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 61 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 62 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 62 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 64) => (natFourIntegerMatrix 8 f416HCompressionInteger) 63 j)
      (fun (_ : Fin 1) (j : Fin 64) => (f416rawHForm) 63 j) (by decide +kernel)
    exact h 0 b

#print axioms f416_HCompression_hM_rows_3
end TorusLean.BosonFiniteCertificate
