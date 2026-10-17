import torus.shared.BosonFiniteCertificateNatFourHS415Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f415_H_source_row_28 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 28) (f415basis b)=f415rawHForm 28 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 28) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 28 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_29 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 29) (f415basis b)=f415rawHForm 29 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 29) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 29 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_30 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 30) (f415basis b)=f415rawHForm 30 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 30) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 30 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_31 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 31) (f415basis b)=f415rawHForm 31 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 31) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 31 b) (by decide +kernel)
  exact h 0

theorem f415_H_rows_7 (a b : Fin 54) (hlo : 28 ≤ a.val) (hhi : a.val < 32) :
    natFourHWordFormSparse 15 (f415basis a) (f415basis b) = f415rawHForm a b := by
  fin_cases a
  · change 28 ≤ (0 : ℕ) at hlo
    omega
  · change 28 ≤ (1 : ℕ) at hlo
    omega
  · change 28 ≤ (2 : ℕ) at hlo
    omega
  · change 28 ≤ (3 : ℕ) at hlo
    omega
  · change 28 ≤ (4 : ℕ) at hlo
    omega
  · change 28 ≤ (5 : ℕ) at hlo
    omega
  · change 28 ≤ (6 : ℕ) at hlo
    omega
  · change 28 ≤ (7 : ℕ) at hlo
    omega
  · change 28 ≤ (8 : ℕ) at hlo
    omega
  · change 28 ≤ (9 : ℕ) at hlo
    omega
  · change 28 ≤ (10 : ℕ) at hlo
    omega
  · change 28 ≤ (11 : ℕ) at hlo
    omega
  · change 28 ≤ (12 : ℕ) at hlo
    omega
  · change 28 ≤ (13 : ℕ) at hlo
    omega
  · change 28 ≤ (14 : ℕ) at hlo
    omega
  · change 28 ≤ (15 : ℕ) at hlo
    omega
  · change 28 ≤ (16 : ℕ) at hlo
    omega
  · change 28 ≤ (17 : ℕ) at hlo
    omega
  · change 28 ≤ (18 : ℕ) at hlo
    omega
  · change 28 ≤ (19 : ℕ) at hlo
    omega
  · change 28 ≤ (20 : ℕ) at hlo
    omega
  · change 28 ≤ (21 : ℕ) at hlo
    omega
  · change 28 ≤ (22 : ℕ) at hlo
    omega
  · change 28 ≤ (23 : ℕ) at hlo
    omega
  · change 28 ≤ (24 : ℕ) at hlo
    omega
  · change 28 ≤ (25 : ℕ) at hlo
    omega
  · change 28 ≤ (26 : ℕ) at hlo
    omega
  · change 28 ≤ (27 : ℕ) at hlo
    omega
  · exact f415_H_source_row_28 b
  · exact f415_H_source_row_29 b
  · exact f415_H_source_row_30 b
  · exact f415_H_source_row_31 b
  · change (32 : ℕ) < 32 at hhi
    omega
  · change (33 : ℕ) < 32 at hhi
    omega
  · change (34 : ℕ) < 32 at hhi
    omega
  · change (35 : ℕ) < 32 at hhi
    omega
  · change (36 : ℕ) < 32 at hhi
    omega
  · change (37 : ℕ) < 32 at hhi
    omega
  · change (38 : ℕ) < 32 at hhi
    omega
  · change (39 : ℕ) < 32 at hhi
    omega
  · change (40 : ℕ) < 32 at hhi
    omega
  · change (41 : ℕ) < 32 at hhi
    omega
  · change (42 : ℕ) < 32 at hhi
    omega
  · change (43 : ℕ) < 32 at hhi
    omega
  · change (44 : ℕ) < 32 at hhi
    omega
  · change (45 : ℕ) < 32 at hhi
    omega
  · change (46 : ℕ) < 32 at hhi
    omega
  · change (47 : ℕ) < 32 at hhi
    omega
  · change (48 : ℕ) < 32 at hhi
    omega
  · change (49 : ℕ) < 32 at hhi
    omega
  · change (50 : ℕ) < 32 at hhi
    omega
  · change (51 : ℕ) < 32 at hhi
    omega
  · change (52 : ℕ) < 32 at hhi
    omega
  · change (53 : ℕ) < 32 at hhi
    omega

#print axioms f415_H_rows_7
end TorusLean.BosonFiniteCertificate
