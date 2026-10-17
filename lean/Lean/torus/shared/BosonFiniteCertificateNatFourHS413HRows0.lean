import torus.shared.BosonFiniteCertificateNatFourHS413Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f413_H_source_row_0 : ∀ b : Fin 39,
    natFourHWordFormSparse 13 (f413basis 0) (f413basis b)=f413rawHForm 0 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) => natFourHWordFormSparse 13 (f413basis 0) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawHForm 0 b) (by decide +kernel)
  exact h 0

private theorem f413_H_source_row_1 : ∀ b : Fin 39,
    natFourHWordFormSparse 13 (f413basis 1) (f413basis b)=f413rawHForm 1 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) => natFourHWordFormSparse 13 (f413basis 1) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawHForm 1 b) (by decide +kernel)
  exact h 0

private theorem f413_H_source_row_2 : ∀ b : Fin 39,
    natFourHWordFormSparse 13 (f413basis 2) (f413basis b)=f413rawHForm 2 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) => natFourHWordFormSparse 13 (f413basis 2) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawHForm 2 b) (by decide +kernel)
  exact h 0

private theorem f413_H_source_row_3 : ∀ b : Fin 39,
    natFourHWordFormSparse 13 (f413basis 3) (f413basis b)=f413rawHForm 3 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) => natFourHWordFormSparse 13 (f413basis 3) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawHForm 3 b) (by decide +kernel)
  exact h 0

private theorem f413_H_source_row_4 : ∀ b : Fin 39,
    natFourHWordFormSparse 13 (f413basis 4) (f413basis b)=f413rawHForm 4 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) => natFourHWordFormSparse 13 (f413basis 4) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawHForm 4 b) (by decide +kernel)
  exact h 0

private theorem f413_H_source_row_5 : ∀ b : Fin 39,
    natFourHWordFormSparse 13 (f413basis 5) (f413basis b)=f413rawHForm 5 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) => natFourHWordFormSparse 13 (f413basis 5) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawHForm 5 b) (by decide +kernel)
  exact h 0

theorem f413_H_rows_0 (a b : Fin 39) (hlo : 0 ≤ a.val) (hhi : a.val < 6) :
    natFourHWordFormSparse 13 (f413basis a) (f413basis b) = f413rawHForm a b := by
  fin_cases a
  · exact f413_H_source_row_0 b
  · exact f413_H_source_row_1 b
  · exact f413_H_source_row_2 b
  · exact f413_H_source_row_3 b
  · exact f413_H_source_row_4 b
  · exact f413_H_source_row_5 b
  · change (6 : ℕ) < 6 at hhi
    omega
  · change (7 : ℕ) < 6 at hhi
    omega
  · change (8 : ℕ) < 6 at hhi
    omega
  · change (9 : ℕ) < 6 at hhi
    omega
  · change (10 : ℕ) < 6 at hhi
    omega
  · change (11 : ℕ) < 6 at hhi
    omega
  · change (12 : ℕ) < 6 at hhi
    omega
  · change (13 : ℕ) < 6 at hhi
    omega
  · change (14 : ℕ) < 6 at hhi
    omega
  · change (15 : ℕ) < 6 at hhi
    omega
  · change (16 : ℕ) < 6 at hhi
    omega
  · change (17 : ℕ) < 6 at hhi
    omega
  · change (18 : ℕ) < 6 at hhi
    omega
  · change (19 : ℕ) < 6 at hhi
    omega
  · change (20 : ℕ) < 6 at hhi
    omega
  · change (21 : ℕ) < 6 at hhi
    omega
  · change (22 : ℕ) < 6 at hhi
    omega
  · change (23 : ℕ) < 6 at hhi
    omega
  · change (24 : ℕ) < 6 at hhi
    omega
  · change (25 : ℕ) < 6 at hhi
    omega
  · change (26 : ℕ) < 6 at hhi
    omega
  · change (27 : ℕ) < 6 at hhi
    omega
  · change (28 : ℕ) < 6 at hhi
    omega
  · change (29 : ℕ) < 6 at hhi
    omega
  · change (30 : ℕ) < 6 at hhi
    omega
  · change (31 : ℕ) < 6 at hhi
    omega
  · change (32 : ℕ) < 6 at hhi
    omega
  · change (33 : ℕ) < 6 at hhi
    omega
  · change (34 : ℕ) < 6 at hhi
    omega
  · change (35 : ℕ) < 6 at hhi
    omega
  · change (36 : ℕ) < 6 at hhi
    omega
  · change (37 : ℕ) < 6 at hhi
    omega
  · change (38 : ℕ) < 6 at hhi
    omega

#print axioms f413_H_rows_0
end TorusLean.BosonFiniteCertificate
