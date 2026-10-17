import torus.shared.BosonFiniteCertificateNatFourHS414HCompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f414_HCompression_hM_rows_1 (a : Fin 47) (hlo : 24 ≤ a.val) (hhi : a.val < 47) (b : Fin 47) :
    (natFourIntegerMatrix 4 f414HCompressionInteger) a b=(f414rawHForm) a b := by
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
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 24 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 24 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 25 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 25 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 26 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 26 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 27 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 27 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 28 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 28 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 29 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 29 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 30 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 30 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 31 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 31 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 32 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 32 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 33 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 33 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 34 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 34 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 35 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 35 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 36 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 36 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 37 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 37 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 38 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 38 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 39 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 39 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 40 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 40 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 41 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 41 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 42 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 42 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 43 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 43 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 44 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 44 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 45 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 45 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 46 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 46 j) (by decide +kernel)
    exact h 0 b

#print axioms f414_HCompression_hM_rows_1
end TorusLean.BosonFiniteCertificate
