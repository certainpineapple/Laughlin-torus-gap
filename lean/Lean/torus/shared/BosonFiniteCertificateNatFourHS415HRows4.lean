import torus.shared.BosonFiniteCertificateNatFourHS415Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f415_H_source_row_16 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 16) (f415basis b)=f415rawHForm 16 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 16) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 16 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_17 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 17) (f415basis b)=f415rawHForm 17 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 17) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 17 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_18 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 18) (f415basis b)=f415rawHForm 18 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 18) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 18 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_19 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 19) (f415basis b)=f415rawHForm 19 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 19) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 19 b) (by decide +kernel)
  exact h 0

theorem f415_H_rows_4 (a b : Fin 54) (hlo : 16 ≤ a.val) (hhi : a.val < 20) :
    natFourHWordFormSparse 15 (f415basis a) (f415basis b) = f415rawHForm a b := by
  fin_cases a
  · change 16 ≤ (0 : ℕ) at hlo
    omega
  · change 16 ≤ (1 : ℕ) at hlo
    omega
  · change 16 ≤ (2 : ℕ) at hlo
    omega
  · change 16 ≤ (3 : ℕ) at hlo
    omega
  · change 16 ≤ (4 : ℕ) at hlo
    omega
  · change 16 ≤ (5 : ℕ) at hlo
    omega
  · change 16 ≤ (6 : ℕ) at hlo
    omega
  · change 16 ≤ (7 : ℕ) at hlo
    omega
  · change 16 ≤ (8 : ℕ) at hlo
    omega
  · change 16 ≤ (9 : ℕ) at hlo
    omega
  · change 16 ≤ (10 : ℕ) at hlo
    omega
  · change 16 ≤ (11 : ℕ) at hlo
    omega
  · change 16 ≤ (12 : ℕ) at hlo
    omega
  · change 16 ≤ (13 : ℕ) at hlo
    omega
  · change 16 ≤ (14 : ℕ) at hlo
    omega
  · change 16 ≤ (15 : ℕ) at hlo
    omega
  · exact f415_H_source_row_16 b
  · exact f415_H_source_row_17 b
  · exact f415_H_source_row_18 b
  · exact f415_H_source_row_19 b
  · change (20 : ℕ) < 20 at hhi
    omega
  · change (21 : ℕ) < 20 at hhi
    omega
  · change (22 : ℕ) < 20 at hhi
    omega
  · change (23 : ℕ) < 20 at hhi
    omega
  · change (24 : ℕ) < 20 at hhi
    omega
  · change (25 : ℕ) < 20 at hhi
    omega
  · change (26 : ℕ) < 20 at hhi
    omega
  · change (27 : ℕ) < 20 at hhi
    omega
  · change (28 : ℕ) < 20 at hhi
    omega
  · change (29 : ℕ) < 20 at hhi
    omega
  · change (30 : ℕ) < 20 at hhi
    omega
  · change (31 : ℕ) < 20 at hhi
    omega
  · change (32 : ℕ) < 20 at hhi
    omega
  · change (33 : ℕ) < 20 at hhi
    omega
  · change (34 : ℕ) < 20 at hhi
    omega
  · change (35 : ℕ) < 20 at hhi
    omega
  · change (36 : ℕ) < 20 at hhi
    omega
  · change (37 : ℕ) < 20 at hhi
    omega
  · change (38 : ℕ) < 20 at hhi
    omega
  · change (39 : ℕ) < 20 at hhi
    omega
  · change (40 : ℕ) < 20 at hhi
    omega
  · change (41 : ℕ) < 20 at hhi
    omega
  · change (42 : ℕ) < 20 at hhi
    omega
  · change (43 : ℕ) < 20 at hhi
    omega
  · change (44 : ℕ) < 20 at hhi
    omega
  · change (45 : ℕ) < 20 at hhi
    omega
  · change (46 : ℕ) < 20 at hhi
    omega
  · change (47 : ℕ) < 20 at hhi
    omega
  · change (48 : ℕ) < 20 at hhi
    omega
  · change (49 : ℕ) < 20 at hhi
    omega
  · change (50 : ℕ) < 20 at hhi
    omega
  · change (51 : ℕ) < 20 at hhi
    omega
  · change (52 : ℕ) < 20 at hhi
    omega
  · change (53 : ℕ) < 20 at hhi
    omega

#print axioms f415_H_rows_4
end TorusLean.BosonFiniteCertificate
