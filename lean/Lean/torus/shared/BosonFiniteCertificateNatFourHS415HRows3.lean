import torus.shared.BosonFiniteCertificateNatFourHS415Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f415_H_source_row_12 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 12) (f415basis b)=f415rawHForm 12 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 12) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 12 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_13 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 13) (f415basis b)=f415rawHForm 13 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 13) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 13 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_14 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 14) (f415basis b)=f415rawHForm 14 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 14) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 14 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_15 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 15) (f415basis b)=f415rawHForm 15 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 15) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 15 b) (by decide +kernel)
  exact h 0

theorem f415_H_rows_3 (a b : Fin 54) (hlo : 12 ≤ a.val) (hhi : a.val < 16) :
    natFourHWordFormSparse 15 (f415basis a) (f415basis b) = f415rawHForm a b := by
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
  · exact f415_H_source_row_12 b
  · exact f415_H_source_row_13 b
  · exact f415_H_source_row_14 b
  · exact f415_H_source_row_15 b
  · change (16 : ℕ) < 16 at hhi
    omega
  · change (17 : ℕ) < 16 at hhi
    omega
  · change (18 : ℕ) < 16 at hhi
    omega
  · change (19 : ℕ) < 16 at hhi
    omega
  · change (20 : ℕ) < 16 at hhi
    omega
  · change (21 : ℕ) < 16 at hhi
    omega
  · change (22 : ℕ) < 16 at hhi
    omega
  · change (23 : ℕ) < 16 at hhi
    omega
  · change (24 : ℕ) < 16 at hhi
    omega
  · change (25 : ℕ) < 16 at hhi
    omega
  · change (26 : ℕ) < 16 at hhi
    omega
  · change (27 : ℕ) < 16 at hhi
    omega
  · change (28 : ℕ) < 16 at hhi
    omega
  · change (29 : ℕ) < 16 at hhi
    omega
  · change (30 : ℕ) < 16 at hhi
    omega
  · change (31 : ℕ) < 16 at hhi
    omega
  · change (32 : ℕ) < 16 at hhi
    omega
  · change (33 : ℕ) < 16 at hhi
    omega
  · change (34 : ℕ) < 16 at hhi
    omega
  · change (35 : ℕ) < 16 at hhi
    omega
  · change (36 : ℕ) < 16 at hhi
    omega
  · change (37 : ℕ) < 16 at hhi
    omega
  · change (38 : ℕ) < 16 at hhi
    omega
  · change (39 : ℕ) < 16 at hhi
    omega
  · change (40 : ℕ) < 16 at hhi
    omega
  · change (41 : ℕ) < 16 at hhi
    omega
  · change (42 : ℕ) < 16 at hhi
    omega
  · change (43 : ℕ) < 16 at hhi
    omega
  · change (44 : ℕ) < 16 at hhi
    omega
  · change (45 : ℕ) < 16 at hhi
    omega
  · change (46 : ℕ) < 16 at hhi
    omega
  · change (47 : ℕ) < 16 at hhi
    omega
  · change (48 : ℕ) < 16 at hhi
    omega
  · change (49 : ℕ) < 16 at hhi
    omega
  · change (50 : ℕ) < 16 at hhi
    omega
  · change (51 : ℕ) < 16 at hhi
    omega
  · change (52 : ℕ) < 16 at hhi
    omega
  · change (53 : ℕ) < 16 at hhi
    omega

#print axioms f415_H_rows_3
end TorusLean.BosonFiniteCertificate
