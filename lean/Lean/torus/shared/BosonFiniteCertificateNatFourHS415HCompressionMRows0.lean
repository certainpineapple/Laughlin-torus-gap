import torus.shared.BosonFiniteCertificateNatFourHS415HCompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f415_HCompression_hM_rows_0 (a : Fin 54) (hlo : 0 ≤ a.val) (hhi : a.val < 18) (b : Fin 54) :
    (natFourIntegerMatrix 4 f415HCompressionInteger) a b=(f415rawHForm) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 0 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 1 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 2 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 3 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 4 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 5 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 6 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 7 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 8 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 9 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 10 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 11 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 12 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 13 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 14 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 15 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 15 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 16 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 54) => (natFourIntegerMatrix 4 f415HCompressionInteger) 17 j)
      (fun (_ : Fin 1) (j : Fin 54) => (f415rawHForm) 17 j) (by decide +kernel)
    exact h 0 b
  · change (18 : ℕ) < 18 at hhi
    omega
  · change (19 : ℕ) < 18 at hhi
    omega
  · change (20 : ℕ) < 18 at hhi
    omega
  · change (21 : ℕ) < 18 at hhi
    omega
  · change (22 : ℕ) < 18 at hhi
    omega
  · change (23 : ℕ) < 18 at hhi
    omega
  · change (24 : ℕ) < 18 at hhi
    omega
  · change (25 : ℕ) < 18 at hhi
    omega
  · change (26 : ℕ) < 18 at hhi
    omega
  · change (27 : ℕ) < 18 at hhi
    omega
  · change (28 : ℕ) < 18 at hhi
    omega
  · change (29 : ℕ) < 18 at hhi
    omega
  · change (30 : ℕ) < 18 at hhi
    omega
  · change (31 : ℕ) < 18 at hhi
    omega
  · change (32 : ℕ) < 18 at hhi
    omega
  · change (33 : ℕ) < 18 at hhi
    omega
  · change (34 : ℕ) < 18 at hhi
    omega
  · change (35 : ℕ) < 18 at hhi
    omega
  · change (36 : ℕ) < 18 at hhi
    omega
  · change (37 : ℕ) < 18 at hhi
    omega
  · change (38 : ℕ) < 18 at hhi
    omega
  · change (39 : ℕ) < 18 at hhi
    omega
  · change (40 : ℕ) < 18 at hhi
    omega
  · change (41 : ℕ) < 18 at hhi
    omega
  · change (42 : ℕ) < 18 at hhi
    omega
  · change (43 : ℕ) < 18 at hhi
    omega
  · change (44 : ℕ) < 18 at hhi
    omega
  · change (45 : ℕ) < 18 at hhi
    omega
  · change (46 : ℕ) < 18 at hhi
    omega
  · change (47 : ℕ) < 18 at hhi
    omega
  · change (48 : ℕ) < 18 at hhi
    omega
  · change (49 : ℕ) < 18 at hhi
    omega
  · change (50 : ℕ) < 18 at hhi
    omega
  · change (51 : ℕ) < 18 at hhi
    omega
  · change (52 : ℕ) < 18 at hhi
    omega
  · change (53 : ℕ) < 18 at hhi
    omega

#print axioms f415_HCompression_hM_rows_0
end TorusLean.BosonFiniteCertificate
