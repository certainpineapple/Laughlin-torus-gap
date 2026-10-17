import torus.shared.BosonFiniteCertificateNatFourHS415Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f415_H_source_row_40 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 40) (f415basis b)=f415rawHForm 40 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 40) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 40 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_41 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 41) (f415basis b)=f415rawHForm 41 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 41) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 41 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_42 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 42) (f415basis b)=f415rawHForm 42 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 42) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 42 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_43 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 43) (f415basis b)=f415rawHForm 43 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 43) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 43 b) (by decide +kernel)
  exact h 0

theorem f415_H_rows_10 (a b : Fin 54) (hlo : 40 ≤ a.val) (hhi : a.val < 44) :
    natFourHWordFormSparse 15 (f415basis a) (f415basis b) = f415rawHForm a b := by
  fin_cases a
  · change 40 ≤ (0 : ℕ) at hlo
    omega
  · change 40 ≤ (1 : ℕ) at hlo
    omega
  · change 40 ≤ (2 : ℕ) at hlo
    omega
  · change 40 ≤ (3 : ℕ) at hlo
    omega
  · change 40 ≤ (4 : ℕ) at hlo
    omega
  · change 40 ≤ (5 : ℕ) at hlo
    omega
  · change 40 ≤ (6 : ℕ) at hlo
    omega
  · change 40 ≤ (7 : ℕ) at hlo
    omega
  · change 40 ≤ (8 : ℕ) at hlo
    omega
  · change 40 ≤ (9 : ℕ) at hlo
    omega
  · change 40 ≤ (10 : ℕ) at hlo
    omega
  · change 40 ≤ (11 : ℕ) at hlo
    omega
  · change 40 ≤ (12 : ℕ) at hlo
    omega
  · change 40 ≤ (13 : ℕ) at hlo
    omega
  · change 40 ≤ (14 : ℕ) at hlo
    omega
  · change 40 ≤ (15 : ℕ) at hlo
    omega
  · change 40 ≤ (16 : ℕ) at hlo
    omega
  · change 40 ≤ (17 : ℕ) at hlo
    omega
  · change 40 ≤ (18 : ℕ) at hlo
    omega
  · change 40 ≤ (19 : ℕ) at hlo
    omega
  · change 40 ≤ (20 : ℕ) at hlo
    omega
  · change 40 ≤ (21 : ℕ) at hlo
    omega
  · change 40 ≤ (22 : ℕ) at hlo
    omega
  · change 40 ≤ (23 : ℕ) at hlo
    omega
  · change 40 ≤ (24 : ℕ) at hlo
    omega
  · change 40 ≤ (25 : ℕ) at hlo
    omega
  · change 40 ≤ (26 : ℕ) at hlo
    omega
  · change 40 ≤ (27 : ℕ) at hlo
    omega
  · change 40 ≤ (28 : ℕ) at hlo
    omega
  · change 40 ≤ (29 : ℕ) at hlo
    omega
  · change 40 ≤ (30 : ℕ) at hlo
    omega
  · change 40 ≤ (31 : ℕ) at hlo
    omega
  · change 40 ≤ (32 : ℕ) at hlo
    omega
  · change 40 ≤ (33 : ℕ) at hlo
    omega
  · change 40 ≤ (34 : ℕ) at hlo
    omega
  · change 40 ≤ (35 : ℕ) at hlo
    omega
  · change 40 ≤ (36 : ℕ) at hlo
    omega
  · change 40 ≤ (37 : ℕ) at hlo
    omega
  · change 40 ≤ (38 : ℕ) at hlo
    omega
  · change 40 ≤ (39 : ℕ) at hlo
    omega
  · exact f415_H_source_row_40 b
  · exact f415_H_source_row_41 b
  · exact f415_H_source_row_42 b
  · exact f415_H_source_row_43 b
  · change (44 : ℕ) < 44 at hhi
    omega
  · change (45 : ℕ) < 44 at hhi
    omega
  · change (46 : ℕ) < 44 at hhi
    omega
  · change (47 : ℕ) < 44 at hhi
    omega
  · change (48 : ℕ) < 44 at hhi
    omega
  · change (49 : ℕ) < 44 at hhi
    omega
  · change (50 : ℕ) < 44 at hhi
    omega
  · change (51 : ℕ) < 44 at hhi
    omega
  · change (52 : ℕ) < 44 at hhi
    omega
  · change (53 : ℕ) < 44 at hhi
    omega

#print axioms f415_H_rows_10
end TorusLean.BosonFiniteCertificate
