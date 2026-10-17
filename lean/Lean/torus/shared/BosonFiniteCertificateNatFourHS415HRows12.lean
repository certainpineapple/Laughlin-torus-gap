import torus.shared.BosonFiniteCertificateNatFourHS415Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f415_H_source_row_48 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 48) (f415basis b)=f415rawHForm 48 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 48) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 48 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_49 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 49) (f415basis b)=f415rawHForm 49 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 49) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 49 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_50 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 50) (f415basis b)=f415rawHForm 50 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 50) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 50 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_51 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 51) (f415basis b)=f415rawHForm 51 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 51) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 51 b) (by decide +kernel)
  exact h 0

theorem f415_H_rows_12 (a b : Fin 54) (hlo : 48 ≤ a.val) (hhi : a.val < 52) :
    natFourHWordFormSparse 15 (f415basis a) (f415basis b) = f415rawHForm a b := by
  fin_cases a
  · change 48 ≤ (0 : ℕ) at hlo
    omega
  · change 48 ≤ (1 : ℕ) at hlo
    omega
  · change 48 ≤ (2 : ℕ) at hlo
    omega
  · change 48 ≤ (3 : ℕ) at hlo
    omega
  · change 48 ≤ (4 : ℕ) at hlo
    omega
  · change 48 ≤ (5 : ℕ) at hlo
    omega
  · change 48 ≤ (6 : ℕ) at hlo
    omega
  · change 48 ≤ (7 : ℕ) at hlo
    omega
  · change 48 ≤ (8 : ℕ) at hlo
    omega
  · change 48 ≤ (9 : ℕ) at hlo
    omega
  · change 48 ≤ (10 : ℕ) at hlo
    omega
  · change 48 ≤ (11 : ℕ) at hlo
    omega
  · change 48 ≤ (12 : ℕ) at hlo
    omega
  · change 48 ≤ (13 : ℕ) at hlo
    omega
  · change 48 ≤ (14 : ℕ) at hlo
    omega
  · change 48 ≤ (15 : ℕ) at hlo
    omega
  · change 48 ≤ (16 : ℕ) at hlo
    omega
  · change 48 ≤ (17 : ℕ) at hlo
    omega
  · change 48 ≤ (18 : ℕ) at hlo
    omega
  · change 48 ≤ (19 : ℕ) at hlo
    omega
  · change 48 ≤ (20 : ℕ) at hlo
    omega
  · change 48 ≤ (21 : ℕ) at hlo
    omega
  · change 48 ≤ (22 : ℕ) at hlo
    omega
  · change 48 ≤ (23 : ℕ) at hlo
    omega
  · change 48 ≤ (24 : ℕ) at hlo
    omega
  · change 48 ≤ (25 : ℕ) at hlo
    omega
  · change 48 ≤ (26 : ℕ) at hlo
    omega
  · change 48 ≤ (27 : ℕ) at hlo
    omega
  · change 48 ≤ (28 : ℕ) at hlo
    omega
  · change 48 ≤ (29 : ℕ) at hlo
    omega
  · change 48 ≤ (30 : ℕ) at hlo
    omega
  · change 48 ≤ (31 : ℕ) at hlo
    omega
  · change 48 ≤ (32 : ℕ) at hlo
    omega
  · change 48 ≤ (33 : ℕ) at hlo
    omega
  · change 48 ≤ (34 : ℕ) at hlo
    omega
  · change 48 ≤ (35 : ℕ) at hlo
    omega
  · change 48 ≤ (36 : ℕ) at hlo
    omega
  · change 48 ≤ (37 : ℕ) at hlo
    omega
  · change 48 ≤ (38 : ℕ) at hlo
    omega
  · change 48 ≤ (39 : ℕ) at hlo
    omega
  · change 48 ≤ (40 : ℕ) at hlo
    omega
  · change 48 ≤ (41 : ℕ) at hlo
    omega
  · change 48 ≤ (42 : ℕ) at hlo
    omega
  · change 48 ≤ (43 : ℕ) at hlo
    omega
  · change 48 ≤ (44 : ℕ) at hlo
    omega
  · change 48 ≤ (45 : ℕ) at hlo
    omega
  · change 48 ≤ (46 : ℕ) at hlo
    omega
  · change 48 ≤ (47 : ℕ) at hlo
    omega
  · exact f415_H_source_row_48 b
  · exact f415_H_source_row_49 b
  · exact f415_H_source_row_50 b
  · exact f415_H_source_row_51 b
  · change (52 : ℕ) < 52 at hhi
    omega
  · change (53 : ℕ) < 52 at hhi
    omega

#print axioms f415_H_rows_12
end TorusLean.BosonFiniteCertificate
