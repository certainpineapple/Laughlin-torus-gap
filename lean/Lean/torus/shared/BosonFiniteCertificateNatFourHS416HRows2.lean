import torus.shared.BosonFiniteCertificateNatFourHS416Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f416_H_source_row_8 : ∀ b : Fin 64,
    natFourHWordFormSparse 16 (f416basis 8) (f416basis b)=f416rawHForm 8 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) => natFourHWordFormSparse 16 (f416basis 8) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawHForm 8 b) (by decide +kernel)
  exact h 0

private theorem f416_H_source_row_9 : ∀ b : Fin 64,
    natFourHWordFormSparse 16 (f416basis 9) (f416basis b)=f416rawHForm 9 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) => natFourHWordFormSparse 16 (f416basis 9) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawHForm 9 b) (by decide +kernel)
  exact h 0

private theorem f416_H_source_row_10 : ∀ b : Fin 64,
    natFourHWordFormSparse 16 (f416basis 10) (f416basis b)=f416rawHForm 10 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) => natFourHWordFormSparse 16 (f416basis 10) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawHForm 10 b) (by decide +kernel)
  exact h 0

private theorem f416_H_source_row_11 : ∀ b : Fin 64,
    natFourHWordFormSparse 16 (f416basis 11) (f416basis b)=f416rawHForm 11 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) => natFourHWordFormSparse 16 (f416basis 11) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawHForm 11 b) (by decide +kernel)
  exact h 0

theorem f416_H_rows_2 (a b : Fin 64) (hlo : 8 ≤ a.val) (hhi : a.val < 12) :
    natFourHWordFormSparse 16 (f416basis a) (f416basis b) = f416rawHForm a b := by
  fin_cases a
  · change 8 ≤ (0 : ℕ) at hlo
    omega
  · change 8 ≤ (1 : ℕ) at hlo
    omega
  · change 8 ≤ (2 : ℕ) at hlo
    omega
  · change 8 ≤ (3 : ℕ) at hlo
    omega
  · change 8 ≤ (4 : ℕ) at hlo
    omega
  · change 8 ≤ (5 : ℕ) at hlo
    omega
  · change 8 ≤ (6 : ℕ) at hlo
    omega
  · change 8 ≤ (7 : ℕ) at hlo
    omega
  · exact f416_H_source_row_8 b
  · exact f416_H_source_row_9 b
  · exact f416_H_source_row_10 b
  · exact f416_H_source_row_11 b
  · change (12 : ℕ) < 12 at hhi
    omega
  · change (13 : ℕ) < 12 at hhi
    omega
  · change (14 : ℕ) < 12 at hhi
    omega
  · change (15 : ℕ) < 12 at hhi
    omega
  · change (16 : ℕ) < 12 at hhi
    omega
  · change (17 : ℕ) < 12 at hhi
    omega
  · change (18 : ℕ) < 12 at hhi
    omega
  · change (19 : ℕ) < 12 at hhi
    omega
  · change (20 : ℕ) < 12 at hhi
    omega
  · change (21 : ℕ) < 12 at hhi
    omega
  · change (22 : ℕ) < 12 at hhi
    omega
  · change (23 : ℕ) < 12 at hhi
    omega
  · change (24 : ℕ) < 12 at hhi
    omega
  · change (25 : ℕ) < 12 at hhi
    omega
  · change (26 : ℕ) < 12 at hhi
    omega
  · change (27 : ℕ) < 12 at hhi
    omega
  · change (28 : ℕ) < 12 at hhi
    omega
  · change (29 : ℕ) < 12 at hhi
    omega
  · change (30 : ℕ) < 12 at hhi
    omega
  · change (31 : ℕ) < 12 at hhi
    omega
  · change (32 : ℕ) < 12 at hhi
    omega
  · change (33 : ℕ) < 12 at hhi
    omega
  · change (34 : ℕ) < 12 at hhi
    omega
  · change (35 : ℕ) < 12 at hhi
    omega
  · change (36 : ℕ) < 12 at hhi
    omega
  · change (37 : ℕ) < 12 at hhi
    omega
  · change (38 : ℕ) < 12 at hhi
    omega
  · change (39 : ℕ) < 12 at hhi
    omega
  · change (40 : ℕ) < 12 at hhi
    omega
  · change (41 : ℕ) < 12 at hhi
    omega
  · change (42 : ℕ) < 12 at hhi
    omega
  · change (43 : ℕ) < 12 at hhi
    omega
  · change (44 : ℕ) < 12 at hhi
    omega
  · change (45 : ℕ) < 12 at hhi
    omega
  · change (46 : ℕ) < 12 at hhi
    omega
  · change (47 : ℕ) < 12 at hhi
    omega
  · change (48 : ℕ) < 12 at hhi
    omega
  · change (49 : ℕ) < 12 at hhi
    omega
  · change (50 : ℕ) < 12 at hhi
    omega
  · change (51 : ℕ) < 12 at hhi
    omega
  · change (52 : ℕ) < 12 at hhi
    omega
  · change (53 : ℕ) < 12 at hhi
    omega
  · change (54 : ℕ) < 12 at hhi
    omega
  · change (55 : ℕ) < 12 at hhi
    omega
  · change (56 : ℕ) < 12 at hhi
    omega
  · change (57 : ℕ) < 12 at hhi
    omega
  · change (58 : ℕ) < 12 at hhi
    omega
  · change (59 : ℕ) < 12 at hhi
    omega
  · change (60 : ℕ) < 12 at hhi
    omega
  · change (61 : ℕ) < 12 at hhi
    omega
  · change (62 : ℕ) < 12 at hhi
    omega
  · change (63 : ℕ) < 12 at hhi
    omega

#print axioms f416_H_rows_2
end TorusLean.BosonFiniteCertificate
