import torus.shared.BosonFiniteCertificateNatFourHS415Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f415_H_source_row_24 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 24) (f415basis b)=f415rawHForm 24 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 24) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 24 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_25 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 25) (f415basis b)=f415rawHForm 25 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 25) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 25 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_26 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 26) (f415basis b)=f415rawHForm 26 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 26) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 26 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_27 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 27) (f415basis b)=f415rawHForm 27 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 27) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 27 b) (by decide +kernel)
  exact h 0

theorem f415_H_rows_6 (a b : Fin 54) (hlo : 24 ≤ a.val) (hhi : a.val < 28) :
    natFourHWordFormSparse 15 (f415basis a) (f415basis b) = f415rawHForm a b := by
  fin_cases a
  · change 24 ≤ (0 : ℕ) at hlo
    omega
  · change 24 ≤ (1 : ℕ) at hlo
    omega
  · change 24 ≤ (2 : ℕ) at hlo
    omega
  · change 24 ≤ (3 : ℕ) at hlo
    omega
  · change 24 ≤ (4 : ℕ) at hlo
    omega
  · change 24 ≤ (5 : ℕ) at hlo
    omega
  · change 24 ≤ (6 : ℕ) at hlo
    omega
  · change 24 ≤ (7 : ℕ) at hlo
    omega
  · change 24 ≤ (8 : ℕ) at hlo
    omega
  · change 24 ≤ (9 : ℕ) at hlo
    omega
  · change 24 ≤ (10 : ℕ) at hlo
    omega
  · change 24 ≤ (11 : ℕ) at hlo
    omega
  · change 24 ≤ (12 : ℕ) at hlo
    omega
  · change 24 ≤ (13 : ℕ) at hlo
    omega
  · change 24 ≤ (14 : ℕ) at hlo
    omega
  · change 24 ≤ (15 : ℕ) at hlo
    omega
  · change 24 ≤ (16 : ℕ) at hlo
    omega
  · change 24 ≤ (17 : ℕ) at hlo
    omega
  · change 24 ≤ (18 : ℕ) at hlo
    omega
  · change 24 ≤ (19 : ℕ) at hlo
    omega
  · change 24 ≤ (20 : ℕ) at hlo
    omega
  · change 24 ≤ (21 : ℕ) at hlo
    omega
  · change 24 ≤ (22 : ℕ) at hlo
    omega
  · change 24 ≤ (23 : ℕ) at hlo
    omega
  · exact f415_H_source_row_24 b
  · exact f415_H_source_row_25 b
  · exact f415_H_source_row_26 b
  · exact f415_H_source_row_27 b
  · change (28 : ℕ) < 28 at hhi
    omega
  · change (29 : ℕ) < 28 at hhi
    omega
  · change (30 : ℕ) < 28 at hhi
    omega
  · change (31 : ℕ) < 28 at hhi
    omega
  · change (32 : ℕ) < 28 at hhi
    omega
  · change (33 : ℕ) < 28 at hhi
    omega
  · change (34 : ℕ) < 28 at hhi
    omega
  · change (35 : ℕ) < 28 at hhi
    omega
  · change (36 : ℕ) < 28 at hhi
    omega
  · change (37 : ℕ) < 28 at hhi
    omega
  · change (38 : ℕ) < 28 at hhi
    omega
  · change (39 : ℕ) < 28 at hhi
    omega
  · change (40 : ℕ) < 28 at hhi
    omega
  · change (41 : ℕ) < 28 at hhi
    omega
  · change (42 : ℕ) < 28 at hhi
    omega
  · change (43 : ℕ) < 28 at hhi
    omega
  · change (44 : ℕ) < 28 at hhi
    omega
  · change (45 : ℕ) < 28 at hhi
    omega
  · change (46 : ℕ) < 28 at hhi
    omega
  · change (47 : ℕ) < 28 at hhi
    omega
  · change (48 : ℕ) < 28 at hhi
    omega
  · change (49 : ℕ) < 28 at hhi
    omega
  · change (50 : ℕ) < 28 at hhi
    omega
  · change (51 : ℕ) < 28 at hhi
    omega
  · change (52 : ℕ) < 28 at hhi
    omega
  · change (53 : ℕ) < 28 at hhi
    omega

#print axioms f415_H_rows_6
end TorusLean.BosonFiniteCertificate
