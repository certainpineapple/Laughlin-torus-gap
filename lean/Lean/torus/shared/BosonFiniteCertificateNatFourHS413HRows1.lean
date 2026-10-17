import torus.shared.BosonFiniteCertificateNatFourHS413Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f413_H_source_row_6 : ∀ b : Fin 39,
    natFourHWordFormSparse 13 (f413basis 6) (f413basis b)=f413rawHForm 6 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) => natFourHWordFormSparse 13 (f413basis 6) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawHForm 6 b) (by decide +kernel)
  exact h 0

private theorem f413_H_source_row_7 : ∀ b : Fin 39,
    natFourHWordFormSparse 13 (f413basis 7) (f413basis b)=f413rawHForm 7 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) => natFourHWordFormSparse 13 (f413basis 7) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawHForm 7 b) (by decide +kernel)
  exact h 0

private theorem f413_H_source_row_8 : ∀ b : Fin 39,
    natFourHWordFormSparse 13 (f413basis 8) (f413basis b)=f413rawHForm 8 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) => natFourHWordFormSparse 13 (f413basis 8) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawHForm 8 b) (by decide +kernel)
  exact h 0

private theorem f413_H_source_row_9 : ∀ b : Fin 39,
    natFourHWordFormSparse 13 (f413basis 9) (f413basis b)=f413rawHForm 9 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) => natFourHWordFormSparse 13 (f413basis 9) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawHForm 9 b) (by decide +kernel)
  exact h 0

private theorem f413_H_source_row_10 : ∀ b : Fin 39,
    natFourHWordFormSparse 13 (f413basis 10) (f413basis b)=f413rawHForm 10 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) => natFourHWordFormSparse 13 (f413basis 10) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawHForm 10 b) (by decide +kernel)
  exact h 0

private theorem f413_H_source_row_11 : ∀ b : Fin 39,
    natFourHWordFormSparse 13 (f413basis 11) (f413basis b)=f413rawHForm 11 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) => natFourHWordFormSparse 13 (f413basis 11) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawHForm 11 b) (by decide +kernel)
  exact h 0

theorem f413_H_rows_1 (a b : Fin 39) (hlo : 6 ≤ a.val) (hhi : a.val < 12) :
    natFourHWordFormSparse 13 (f413basis a) (f413basis b) = f413rawHForm a b := by
  fin_cases a
  · change 6 ≤ (0 : ℕ) at hlo
    omega
  · change 6 ≤ (1 : ℕ) at hlo
    omega
  · change 6 ≤ (2 : ℕ) at hlo
    omega
  · change 6 ≤ (3 : ℕ) at hlo
    omega
  · change 6 ≤ (4 : ℕ) at hlo
    omega
  · change 6 ≤ (5 : ℕ) at hlo
    omega
  · exact f413_H_source_row_6 b
  · exact f413_H_source_row_7 b
  · exact f413_H_source_row_8 b
  · exact f413_H_source_row_9 b
  · exact f413_H_source_row_10 b
  · exact f413_H_source_row_11 b
  · change (12 : ℕ) < 12 at hhi
    omega
  · change (13 : ℕ) < 12 at hhi
    omega
  · change (14 : ℕ) < 12 at hhi
    omega
  · change (15 : ℕ) < 12 at hhi
    omega
  · change (16 : ℕ) < 12 at hhi
    omega
  · change (17 : ℕ) < 12 at hhi
    omega
  · change (18 : ℕ) < 12 at hhi
    omega
  · change (19 : ℕ) < 12 at hhi
    omega
  · change (20 : ℕ) < 12 at hhi
    omega
  · change (21 : ℕ) < 12 at hhi
    omega
  · change (22 : ℕ) < 12 at hhi
    omega
  · change (23 : ℕ) < 12 at hhi
    omega
  · change (24 : ℕ) < 12 at hhi
    omega
  · change (25 : ℕ) < 12 at hhi
    omega
  · change (26 : ℕ) < 12 at hhi
    omega
  · change (27 : ℕ) < 12 at hhi
    omega
  · change (28 : ℕ) < 12 at hhi
    omega
  · change (29 : ℕ) < 12 at hhi
    omega
  · change (30 : ℕ) < 12 at hhi
    omega
  · change (31 : ℕ) < 12 at hhi
    omega
  · change (32 : ℕ) < 12 at hhi
    omega
  · change (33 : ℕ) < 12 at hhi
    omega
  · change (34 : ℕ) < 12 at hhi
    omega
  · change (35 : ℕ) < 12 at hhi
    omega
  · change (36 : ℕ) < 12 at hhi
    omega
  · change (37 : ℕ) < 12 at hhi
    omega
  · change (38 : ℕ) < 12 at hhi
    omega

#print axioms f413_H_rows_1
end TorusLean.BosonFiniteCertificate
