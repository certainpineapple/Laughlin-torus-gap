import torus.shared.BosonFiniteCertificateNatFourHS415Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f415_H_source_row_32 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 32) (f415basis b)=f415rawHForm 32 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 32) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 32 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_33 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 33) (f415basis b)=f415rawHForm 33 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 33) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 33 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_34 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 34) (f415basis b)=f415rawHForm 34 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 34) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 34 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_35 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 35) (f415basis b)=f415rawHForm 35 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 35) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 35 b) (by decide +kernel)
  exact h 0

theorem f415_H_rows_8 (a b : Fin 54) (hlo : 32 ≤ a.val) (hhi : a.val < 36) :
    natFourHWordFormSparse 15 (f415basis a) (f415basis b) = f415rawHForm a b := by
  fin_cases a
  · change 32 ≤ (0 : ℕ) at hlo
    omega
  · change 32 ≤ (1 : ℕ) at hlo
    omega
  · change 32 ≤ (2 : ℕ) at hlo
    omega
  · change 32 ≤ (3 : ℕ) at hlo
    omega
  · change 32 ≤ (4 : ℕ) at hlo
    omega
  · change 32 ≤ (5 : ℕ) at hlo
    omega
  · change 32 ≤ (6 : ℕ) at hlo
    omega
  · change 32 ≤ (7 : ℕ) at hlo
    omega
  · change 32 ≤ (8 : ℕ) at hlo
    omega
  · change 32 ≤ (9 : ℕ) at hlo
    omega
  · change 32 ≤ (10 : ℕ) at hlo
    omega
  · change 32 ≤ (11 : ℕ) at hlo
    omega
  · change 32 ≤ (12 : ℕ) at hlo
    omega
  · change 32 ≤ (13 : ℕ) at hlo
    omega
  · change 32 ≤ (14 : ℕ) at hlo
    omega
  · change 32 ≤ (15 : ℕ) at hlo
    omega
  · change 32 ≤ (16 : ℕ) at hlo
    omega
  · change 32 ≤ (17 : ℕ) at hlo
    omega
  · change 32 ≤ (18 : ℕ) at hlo
    omega
  · change 32 ≤ (19 : ℕ) at hlo
    omega
  · change 32 ≤ (20 : ℕ) at hlo
    omega
  · change 32 ≤ (21 : ℕ) at hlo
    omega
  · change 32 ≤ (22 : ℕ) at hlo
    omega
  · change 32 ≤ (23 : ℕ) at hlo
    omega
  · change 32 ≤ (24 : ℕ) at hlo
    omega
  · change 32 ≤ (25 : ℕ) at hlo
    omega
  · change 32 ≤ (26 : ℕ) at hlo
    omega
  · change 32 ≤ (27 : ℕ) at hlo
    omega
  · change 32 ≤ (28 : ℕ) at hlo
    omega
  · change 32 ≤ (29 : ℕ) at hlo
    omega
  · change 32 ≤ (30 : ℕ) at hlo
    omega
  · change 32 ≤ (31 : ℕ) at hlo
    omega
  · exact f415_H_source_row_32 b
  · exact f415_H_source_row_33 b
  · exact f415_H_source_row_34 b
  · exact f415_H_source_row_35 b
  · change (36 : ℕ) < 36 at hhi
    omega
  · change (37 : ℕ) < 36 at hhi
    omega
  · change (38 : ℕ) < 36 at hhi
    omega
  · change (39 : ℕ) < 36 at hhi
    omega
  · change (40 : ℕ) < 36 at hhi
    omega
  · change (41 : ℕ) < 36 at hhi
    omega
  · change (42 : ℕ) < 36 at hhi
    omega
  · change (43 : ℕ) < 36 at hhi
    omega
  · change (44 : ℕ) < 36 at hhi
    omega
  · change (45 : ℕ) < 36 at hhi
    omega
  · change (46 : ℕ) < 36 at hhi
    omega
  · change (47 : ℕ) < 36 at hhi
    omega
  · change (48 : ℕ) < 36 at hhi
    omega
  · change (49 : ℕ) < 36 at hhi
    omega
  · change (50 : ℕ) < 36 at hhi
    omega
  · change (51 : ℕ) < 36 at hhi
    omega
  · change (52 : ℕ) < 36 at hhi
    omega
  · change (53 : ℕ) < 36 at hhi
    omega

#print axioms f415_H_rows_8
end TorusLean.BosonFiniteCertificate
