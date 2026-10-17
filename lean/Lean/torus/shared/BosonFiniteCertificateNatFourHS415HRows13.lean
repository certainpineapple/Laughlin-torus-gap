import torus.shared.BosonFiniteCertificateNatFourHS415Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f415_H_source_row_52 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 52) (f415basis b)=f415rawHForm 52 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 52) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 52 b) (by decide +kernel)
  exact h 0

private theorem f415_H_source_row_53 : ∀ b : Fin 54,
    natFourHWordFormSparse 15 (f415basis 53) (f415basis b)=f415rawHForm 53 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 54) => natFourHWordFormSparse 15 (f415basis 53) (f415basis b))
    (fun (_ : Fin 1) (b : Fin 54) => f415rawHForm 53 b) (by decide +kernel)
  exact h 0

theorem f415_H_rows_13 (a b : Fin 54) (hlo : 52 ≤ a.val) (hhi : a.val < 54) :
    natFourHWordFormSparse 15 (f415basis a) (f415basis b) = f415rawHForm a b := by
  fin_cases a
  · change 52 ≤ (0 : ℕ) at hlo
    omega
  · change 52 ≤ (1 : ℕ) at hlo
    omega
  · change 52 ≤ (2 : ℕ) at hlo
    omega
  · change 52 ≤ (3 : ℕ) at hlo
    omega
  · change 52 ≤ (4 : ℕ) at hlo
    omega
  · change 52 ≤ (5 : ℕ) at hlo
    omega
  · change 52 ≤ (6 : ℕ) at hlo
    omega
  · change 52 ≤ (7 : ℕ) at hlo
    omega
  · change 52 ≤ (8 : ℕ) at hlo
    omega
  · change 52 ≤ (9 : ℕ) at hlo
    omega
  · change 52 ≤ (10 : ℕ) at hlo
    omega
  · change 52 ≤ (11 : ℕ) at hlo
    omega
  · change 52 ≤ (12 : ℕ) at hlo
    omega
  · change 52 ≤ (13 : ℕ) at hlo
    omega
  · change 52 ≤ (14 : ℕ) at hlo
    omega
  · change 52 ≤ (15 : ℕ) at hlo
    omega
  · change 52 ≤ (16 : ℕ) at hlo
    omega
  · change 52 ≤ (17 : ℕ) at hlo
    omega
  · change 52 ≤ (18 : ℕ) at hlo
    omega
  · change 52 ≤ (19 : ℕ) at hlo
    omega
  · change 52 ≤ (20 : ℕ) at hlo
    omega
  · change 52 ≤ (21 : ℕ) at hlo
    omega
  · change 52 ≤ (22 : ℕ) at hlo
    omega
  · change 52 ≤ (23 : ℕ) at hlo
    omega
  · change 52 ≤ (24 : ℕ) at hlo
    omega
  · change 52 ≤ (25 : ℕ) at hlo
    omega
  · change 52 ≤ (26 : ℕ) at hlo
    omega
  · change 52 ≤ (27 : ℕ) at hlo
    omega
  · change 52 ≤ (28 : ℕ) at hlo
    omega
  · change 52 ≤ (29 : ℕ) at hlo
    omega
  · change 52 ≤ (30 : ℕ) at hlo
    omega
  · change 52 ≤ (31 : ℕ) at hlo
    omega
  · change 52 ≤ (32 : ℕ) at hlo
    omega
  · change 52 ≤ (33 : ℕ) at hlo
    omega
  · change 52 ≤ (34 : ℕ) at hlo
    omega
  · change 52 ≤ (35 : ℕ) at hlo
    omega
  · change 52 ≤ (36 : ℕ) at hlo
    omega
  · change 52 ≤ (37 : ℕ) at hlo
    omega
  · change 52 ≤ (38 : ℕ) at hlo
    omega
  · change 52 ≤ (39 : ℕ) at hlo
    omega
  · change 52 ≤ (40 : ℕ) at hlo
    omega
  · change 52 ≤ (41 : ℕ) at hlo
    omega
  · change 52 ≤ (42 : ℕ) at hlo
    omega
  · change 52 ≤ (43 : ℕ) at hlo
    omega
  · change 52 ≤ (44 : ℕ) at hlo
    omega
  · change 52 ≤ (45 : ℕ) at hlo
    omega
  · change 52 ≤ (46 : ℕ) at hlo
    omega
  · change 52 ≤ (47 : ℕ) at hlo
    omega
  · change 52 ≤ (48 : ℕ) at hlo
    omega
  · change 52 ≤ (49 : ℕ) at hlo
    omega
  · change 52 ≤ (50 : ℕ) at hlo
    omega
  · change 52 ≤ (51 : ℕ) at hlo
    omega
  · exact f415_H_source_row_52 b
  · exact f415_H_source_row_53 b

#print axioms f415_H_rows_13
end TorusLean.BosonFiniteCertificate
