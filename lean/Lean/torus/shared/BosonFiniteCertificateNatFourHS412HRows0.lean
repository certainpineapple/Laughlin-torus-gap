import torus.shared.BosonFiniteCertificateNatFourHS412Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f412_H_source_row_0 : ∀ b : Fin 34,
    natFourHWordFormSparse 12 (f412basis 0) (f412basis b)=f412rawHForm 0 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) => natFourHWordFormSparse 12 (f412basis 0) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawHForm 0 b) (by decide +kernel)
  exact h 0

private theorem f412_H_source_row_1 : ∀ b : Fin 34,
    natFourHWordFormSparse 12 (f412basis 1) (f412basis b)=f412rawHForm 1 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) => natFourHWordFormSparse 12 (f412basis 1) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawHForm 1 b) (by decide +kernel)
  exact h 0

private theorem f412_H_source_row_2 : ∀ b : Fin 34,
    natFourHWordFormSparse 12 (f412basis 2) (f412basis b)=f412rawHForm 2 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) => natFourHWordFormSparse 12 (f412basis 2) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawHForm 2 b) (by decide +kernel)
  exact h 0

private theorem f412_H_source_row_3 : ∀ b : Fin 34,
    natFourHWordFormSparse 12 (f412basis 3) (f412basis b)=f412rawHForm 3 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) => natFourHWordFormSparse 12 (f412basis 3) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawHForm 3 b) (by decide +kernel)
  exact h 0

private theorem f412_H_source_row_4 : ∀ b : Fin 34,
    natFourHWordFormSparse 12 (f412basis 4) (f412basis b)=f412rawHForm 4 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) => natFourHWordFormSparse 12 (f412basis 4) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawHForm 4 b) (by decide +kernel)
  exact h 0

private theorem f412_H_source_row_5 : ∀ b : Fin 34,
    natFourHWordFormSparse 12 (f412basis 5) (f412basis b)=f412rawHForm 5 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 34) => natFourHWordFormSparse 12 (f412basis 5) (f412basis b))
    (fun (_ : Fin 1) (b : Fin 34) => f412rawHForm 5 b) (by decide +kernel)
  exact h 0

theorem f412_H_rows_0 (a b : Fin 34) (hlo : 0 ≤ a.val) (hhi : a.val < 6) :
    natFourHWordFormSparse 12 (f412basis a) (f412basis b) = f412rawHForm a b := by
  fin_cases a
  · exact f412_H_source_row_0 b
  · exact f412_H_source_row_1 b
  · exact f412_H_source_row_2 b
  · exact f412_H_source_row_3 b
  · exact f412_H_source_row_4 b
  · exact f412_H_source_row_5 b
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

#print axioms f412_H_rows_0
end TorusLean.BosonFiniteCertificate
