import torus.shared.BosonFiniteCertificateNatFourHS415HCompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f415_HCompression_hM_rows_1 (a : Fin 54) (hlo : 18 ≤ a.val) (hhi : a.val < 36) (b : Fin 54) :
    (natFourIntegerMatrix 4 f415HCompressionInteger) a b=(f415rawHForm) a b := by
  fin_cases a
  · change 18 ≤ (0 : ℕ) at hlo
    omega
  · change 18 ≤ (1 : ℕ) at hlo
    omega
  · change 18 ≤ (2 : ℕ) at hlo
    omega
  · change 18 ≤ (3 : ℕ) at hlo
    omega
  · change 18 ≤ (4 : ℕ) at hlo
    omega
  · change 18 ≤ (5 : ℕ) at hlo
    omega
  · change 18 ≤ (6 : ℕ) at hlo
    omega
  · change 18 ≤ (7 : ℕ) at hlo
    omega
  · change 18 ≤ (8 : ℕ) at hlo
    omega
  · change 18 ≤ (9 : ℕ) at hlo
    omega
  · change 18 ≤ (10 : ℕ) at hlo
    omega
  · change 18 ≤ (11 : ℕ) at hlo
    omega
  · change 18 ≤ (12 : ℕ) at hlo
    omega
  · change 18 ≤ (13 : ℕ) at hlo
    omega
  · change 18 ≤ (14 : ℕ) at hlo
    omega
  · change 18 ≤ (15 : ℕ) at hlo
    omega
  · change 18 ≤ (16 : ℕ) at hlo
    omega
  · change 18 ≤ (17 : ℕ) at hlo
    omega
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 18 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 18 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 19 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 19 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 20 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 20 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 21 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 21 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 22 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 22 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 23 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 23 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 24 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 24 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 25 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 25 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 26 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 26 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 27 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 27 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 28 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 28 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 29 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 29 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 30 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 30 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 31 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 31 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 32 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 32 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 33 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 33 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 34 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 34 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 35 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 35 j) (by decide +kernel)
    exact h 0 b
  · change (36 : ℕ) < 36 at hhi
    omega
  · change (37 : ℕ) < 36 at hhi
    omega
  · change (38 : ℕ) < 36 at hhi
    omega
  · change (39 : ℕ) < 36 at hhi
    omega
  · change (40 : ℕ) < 36 at hhi
    omega
  · change (41 : ℕ) < 36 at hhi
    omega
  · change (42 : ℕ) < 36 at hhi
    omega
  · change (43 : ℕ) < 36 at hhi
    omega
  · change (44 : ℕ) < 36 at hhi
    omega
  · change (45 : ℕ) < 36 at hhi
    omega
  · change (46 : ℕ) < 36 at hhi
    omega
  · change (47 : ℕ) < 36 at hhi
    omega
  · change (48 : ℕ) < 36 at hhi
    omega
  · change (49 : ℕ) < 36 at hhi
    omega
  · change (50 : ℕ) < 36 at hhi
    omega
  · change (51 : ℕ) < 36 at hhi
    omega
  · change (52 : ℕ) < 36 at hhi
    omega
  · change (53 : ℕ) < 36 at hhi
    omega

#print axioms f415_HCompression_hM_rows_1
end TorusLean.BosonFiniteCertificate
