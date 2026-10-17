import torus.shared.BosonFiniteCertificateNatFourHS415Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f415_H_source_row_4 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 4) (f415basis b)=f415rawHForm 4 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 4) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 4 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_5 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 5) (f415basis b)=f415rawHForm 5 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 5) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 5 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_6 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 6) (f415basis b)=f415rawHForm 6 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 6) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 6 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_7 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 7) (f415basis b)=f415rawHForm 7 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 7) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 7 b) (by decide +kernel)
  exact h 0

theorem f415_H_rows_1 (a b : Fin 54) (hlo : 4 ≤ a.val) (hhi : a.val < 8) :
    natFourHWordFormSparse 15 (f415basis a) (f415basis b) = f415rawHForm a b := by
  fin_cases a
  · change 4 ≤ (0 : ℕ) at hlo
    omega
  · change 4 ≤ (1 : ℕ) at hlo
    omega
  · change 4 ≤ (2 : ℕ) at hlo
    omega
  · change 4 ≤ (3 : ℕ) at hlo
    omega
  · exact f415_H_source_row_4 b
  · exact f415_H_source_row_5 b
  · exact f415_H_source_row_6 b
  · exact f415_H_source_row_7 b
  · change (8 : ℕ) < 8 at hhi
    omega
  · change (9 : ℕ) < 8 at hhi
    omega
  · change (10 : ℕ) < 8 at hhi
    omega
  · change (11 : ℕ) < 8 at hhi
    omega
  · change (12 : ℕ) < 8 at hhi
    omega
  · change (13 : ℕ) < 8 at hhi
    omega
  · change (14 : ℕ) < 8 at hhi
    omega
  · change (15 : ℕ) < 8 at hhi
    omega
  · change (16 : ℕ) < 8 at hhi
    omega
  · change (17 : ℕ) < 8 at hhi
    omega
  · change (18 : ℕ) < 8 at hhi
    omega
  · change (19 : ℕ) < 8 at hhi
    omega
  · change (20 : ℕ) < 8 at hhi
    omega
  · change (21 : ℕ) < 8 at hhi
    omega
  · change (22 : ℕ) < 8 at hhi
    omega
  · change (23 : ℕ) < 8 at hhi
    omega
  · change (24 : ℕ) < 8 at hhi
    omega
  · change (25 : ℕ) < 8 at hhi
    omega
  · change (26 : ℕ) < 8 at hhi
    omega
  · change (27 : ℕ) < 8 at hhi
    omega
  · change (28 : ℕ) < 8 at hhi
    omega
  · change (29 : ℕ) < 8 at hhi
    omega
  · change (30 : ℕ) < 8 at hhi
    omega
  · change (31 : ℕ) < 8 at hhi
    omega
  · change (32 : ℕ) < 8 at hhi
    omega
  · change (33 : ℕ) < 8 at hhi
    omega
  · change (34 : ℕ) < 8 at hhi
    omega
  · change (35 : ℕ) < 8 at hhi
    omega
  · change (36 : ℕ) < 8 at hhi
    omega
  · change (37 : ℕ) < 8 at hhi
    omega
  · change (38 : ℕ) < 8 at hhi
    omega
  · change (39 : ℕ) < 8 at hhi
    omega
  · change (40 : ℕ) < 8 at hhi
    omega
  · change (41 : ℕ) < 8 at hhi
    omega
  · change (42 : ℕ) < 8 at hhi
    omega
  · change (43 : ℕ) < 8 at hhi
    omega
  · change (44 : ℕ) < 8 at hhi
    omega
  · change (45 : ℕ) < 8 at hhi
    omega
  · change (46 : ℕ) < 8 at hhi
    omega
  · change (47 : ℕ) < 8 at hhi
    omega
  · change (48 : ℕ) < 8 at hhi
    omega
  · change (49 : ℕ) < 8 at hhi
    omega
  · change (50 : ℕ) < 8 at hhi
    omega
  · change (51 : ℕ) < 8 at hhi
    omega
  · change (52 : ℕ) < 8 at hhi
    omega
  · change (53 : ℕ) < 8 at hhi
    omega

#print axioms f415_H_rows_1
end TorusLean.BosonFiniteCertificate
