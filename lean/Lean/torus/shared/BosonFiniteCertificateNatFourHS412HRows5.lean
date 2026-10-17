import torus.shared.BosonFiniteCertificateNatFourHS412Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f412_H_source_row_30 : ∀ b : Fin 34,
    natFourHWordFormSparse 12 (f412basis 30) (f412basis b)=f412rawHForm 30 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) => natFourHWordFormSparse 12 (f412basis 30) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawHForm 30 b) (by decide +kernel)
  exact h 0

private theorem f412_H_source_row_31 : ∀ b : Fin 34,
    natFourHWordFormSparse 12 (f412basis 31) (f412basis b)=f412rawHForm 31 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) => natFourHWordFormSparse 12 (f412basis 31) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawHForm 31 b) (by decide +kernel)
  exact h 0

private theorem f412_H_source_row_32 : ∀ b : Fin 34,
    natFourHWordFormSparse 12 (f412basis 32) (f412basis b)=f412rawHForm 32 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) => natFourHWordFormSparse 12 (f412basis 32) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawHForm 32 b) (by decide +kernel)
  exact h 0

private theorem f412_H_source_row_33 : ∀ b : Fin 34,
    natFourHWordFormSparse 12 (f412basis 33) (f412basis b)=f412rawHForm 33 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) => natFourHWordFormSparse 12 (f412basis 33) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawHForm 33 b) (by decide +kernel)
  exact h 0

theorem f412_H_rows_5 (a b : Fin 34) (hlo : 30 ≤ a.val) (hhi : a.val < 34) :
    natFourHWordFormSparse 12 (f412basis a) (f412basis b) = f412rawHForm a b := by
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
  · exact f412_H_source_row_30 b
  · exact f412_H_source_row_31 b
  · exact f412_H_source_row_32 b
  · exact f412_H_source_row_33 b

#print axioms f412_H_rows_5
end TorusLean.BosonFiniteCertificate
