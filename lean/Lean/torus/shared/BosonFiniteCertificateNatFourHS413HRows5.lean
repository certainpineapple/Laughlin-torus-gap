import torus.shared.BosonFiniteCertificateNatFourHS413Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f413_H_source_row_30 : ∀ b : Fin 39,
    natFourHWordFormSparse 13 (f413basis 30) (f413basis b)=f413rawHForm 30 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) => natFourHWordFormSparse 13 (f413basis 30) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawHForm 30 b) (by decide +kernel)
  exact h 0

private theorem f413_H_source_row_31 : ∀ b : Fin 39,
    natFourHWordFormSparse 13 (f413basis 31) (f413basis b)=f413rawHForm 31 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) => natFourHWordFormSparse 13 (f413basis 31) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawHForm 31 b) (by decide +kernel)
  exact h 0

private theorem f413_H_source_row_32 : ∀ b : Fin 39,
    natFourHWordFormSparse 13 (f413basis 32) (f413basis b)=f413rawHForm 32 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) => natFourHWordFormSparse 13 (f413basis 32) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawHForm 32 b) (by decide +kernel)
  exact h 0

private theorem f413_H_source_row_33 : ∀ b : Fin 39,
    natFourHWordFormSparse 13 (f413basis 33) (f413basis b)=f413rawHForm 33 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) => natFourHWordFormSparse 13 (f413basis 33) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawHForm 33 b) (by decide +kernel)
  exact h 0

private theorem f413_H_source_row_34 : ∀ b : Fin 39,
    natFourHWordFormSparse 13 (f413basis 34) (f413basis b)=f413rawHForm 34 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) => natFourHWordFormSparse 13 (f413basis 34) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawHForm 34 b) (by decide +kernel)
  exact h 0

private theorem f413_H_source_row_35 : ∀ b : Fin 39,
    natFourHWordFormSparse 13 (f413basis 35) (f413basis b)=f413rawHForm 35 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 39) => natFourHWordFormSparse 13 (f413basis 35) (f413basis b))
    (fun (_ : Fin 1) (b : Fin 39) => f413rawHForm 35 b) (by decide +kernel)
  exact h 0

theorem f413_H_rows_5 (a b : Fin 39) (hlo : 30 ≤ a.val) (hhi : a.val < 36) :
    natFourHWordFormSparse 13 (f413basis a) (f413basis b) = f413rawHForm a b := by
  fin_cases a
  · change 30 ≤ (0 : ℕ) at hlo
    omega
  · change 30 ≤ (1 : ℕ) at hlo
    omega
  · change 30 ≤ (2 : ℕ) at hlo
    omega
  · change 30 ≤ (3 : ℕ) at hlo
    omega
  · change 30 ≤ (4 : ℕ) at hlo
    omega
  · change 30 ≤ (5 : ℕ) at hlo
    omega
  · change 30 ≤ (6 : ℕ) at hlo
    omega
  · change 30 ≤ (7 : ℕ) at hlo
    omega
  · change 30 ≤ (8 : ℕ) at hlo
    omega
  · change 30 ≤ (9 : ℕ) at hlo
    omega
  · change 30 ≤ (10 : ℕ) at hlo
    omega
  · change 30 ≤ (11 : ℕ) at hlo
    omega
  · change 30 ≤ (12 : ℕ) at hlo
    omega
  · change 30 ≤ (13 : ℕ) at hlo
    omega
  · change 30 ≤ (14 : ℕ) at hlo
    omega
  · change 30 ≤ (15 : ℕ) at hlo
    omega
  · change 30 ≤ (16 : ℕ) at hlo
    omega
  · change 30 ≤ (17 : ℕ) at hlo
    omega
  · change 30 ≤ (18 : ℕ) at hlo
    omega
  · change 30 ≤ (19 : ℕ) at hlo
    omega
  · change 30 ≤ (20 : ℕ) at hlo
    omega
  · change 30 ≤ (21 : ℕ) at hlo
    omega
  · change 30 ≤ (22 : ℕ) at hlo
    omega
  · change 30 ≤ (23 : ℕ) at hlo
    omega
  · change 30 ≤ (24 : ℕ) at hlo
    omega
  · change 30 ≤ (25 : ℕ) at hlo
    omega
  · change 30 ≤ (26 : ℕ) at hlo
    omega
  · change 30 ≤ (27 : ℕ) at hlo
    omega
  · change 30 ≤ (28 : ℕ) at hlo
    omega
  · change 30 ≤ (29 : ℕ) at hlo
    omega
  · exact f413_H_source_row_30 b
  · exact f413_H_source_row_31 b
  · exact f413_H_source_row_32 b
  · exact f413_H_source_row_33 b
  · exact f413_H_source_row_34 b
  · exact f413_H_source_row_35 b
  · change (36 : ℕ) < 36 at hhi
    omega
  · change (37 : ℕ) < 36 at hhi
    omega
  · change (38 : ℕ) < 36 at hhi
    omega

#print axioms f413_H_rows_5
end TorusLean.BosonFiniteCertificate
