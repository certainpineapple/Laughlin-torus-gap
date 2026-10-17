import torus.shared.BosonFiniteCertificateNatFourHS412Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f412_H_source_row_12 : ∀ b : Fin 34,
    natFourHWordFormSparse 12 (f412basis 12) (f412basis b)=f412rawHForm 12 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) => natFourHWordFormSparse 12 (f412basis 12) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawHForm 12 b) (by decide +kernel)
  exact h 0

private theorem f412_H_source_row_13 : ∀ b : Fin 34,
    natFourHWordFormSparse 12 (f412basis 13) (f412basis b)=f412rawHForm 13 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) => natFourHWordFormSparse 12 (f412basis 13) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawHForm 13 b) (by decide +kernel)
  exact h 0

private theorem f412_H_source_row_14 : ∀ b : Fin 34,
    natFourHWordFormSparse 12 (f412basis 14) (f412basis b)=f412rawHForm 14 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) => natFourHWordFormSparse 12 (f412basis 14) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawHForm 14 b) (by decide +kernel)
  exact h 0

private theorem f412_H_source_row_15 : ∀ b : Fin 34,
    natFourHWordFormSparse 12 (f412basis 15) (f412basis b)=f412rawHForm 15 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) => natFourHWordFormSparse 12 (f412basis 15) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawHForm 15 b) (by decide +kernel)
  exact h 0

private theorem f412_H_source_row_16 : ∀ b : Fin 34,
    natFourHWordFormSparse 12 (f412basis 16) (f412basis b)=f412rawHForm 16 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) => natFourHWordFormSparse 12 (f412basis 16) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawHForm 16 b) (by decide +kernel)
  exact h 0

private theorem f412_H_source_row_17 : ∀ b : Fin 34,
    natFourHWordFormSparse 12 (f412basis 17) (f412basis b)=f412rawHForm 17 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) => natFourHWordFormSparse 12 (f412basis 17) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawHForm 17 b) (by decide +kernel)
  exact h 0

theorem f412_H_rows_2 (a b : Fin 34) (hlo : 12 ≤ a.val) (hhi : a.val < 18) :
    natFourHWordFormSparse 12 (f412basis a) (f412basis b) = f412rawHForm a b := by
  fin_cases a
  · change 12 ≤ (0 : ℕ) at hlo
    omega
  · change 12 ≤ (1 : ℕ) at hlo
    omega
  · change 12 ≤ (2 : ℕ) at hlo
    omega
  · change 12 ≤ (3 : ℕ) at hlo
    omega
  · change 12 ≤ (4 : ℕ) at hlo
    omega
  · change 12 ≤ (5 : ℕ) at hlo
    omega
  · change 12 ≤ (6 : ℕ) at hlo
    omega
  · change 12 ≤ (7 : ℕ) at hlo
    omega
  · change 12 ≤ (8 : ℕ) at hlo
    omega
  · change 12 ≤ (9 : ℕ) at hlo
    omega
  · change 12 ≤ (10 : ℕ) at hlo
    omega
  · change 12 ≤ (11 : ℕ) at hlo
    omega
  · exact f412_H_source_row_12 b
  · exact f412_H_source_row_13 b
  · exact f412_H_source_row_14 b
  · exact f412_H_source_row_15 b
  · exact f412_H_source_row_16 b
  · exact f412_H_source_row_17 b
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

#print axioms f412_H_rows_2
end TorusLean.BosonFiniteCertificate
