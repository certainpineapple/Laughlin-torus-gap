import torus.shared.BosonFiniteCertificateNatFourHS414HCompressionData

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f414_HCompression_hM_rows_0 (a : Fin 47) (hlo : 0 ≤ a.val) (hhi : a.val < 24) (b : Fin 47) :
    (natFourIntegerMatrix 4 f414HCompressionInteger) a b=(f414rawHForm) a b := by
  fin_cases a
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 0 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 0 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 1 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 1 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 2 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 2 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 3 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 3 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 4 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 4 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 5 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 5 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 6 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 6 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 7 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 7 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 8 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 8 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 9 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 9 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 10 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 10 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 11 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 11 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 12 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 12 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 13 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 13 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 14 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 14 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 15 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 15 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 16 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 16 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 17 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 17 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 18 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 18 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 19 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 19 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 20 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 20 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 21 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 21 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 22 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 22 j) (by decide +kernel)
    exact h 0 b
  · have h := natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (j : Fin 47) => (natFourIntegerMatrix 4 f414HCompressionInteger) 23 j)
      (fun (_ : Fin 1) (j : Fin 47) => (f414rawHForm) 23 j) (by decide +kernel)
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

#print axioms f414_HCompression_hM_rows_0
end TorusLean.BosonFiniteCertificate
