import torus.shared.BosonFiniteCertificateNatFourHS416Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f416_H_source_row_0 : ∀ b : Fin 64,
    natFourHWordFormSparse 16 (f416basis 0) (f416basis b)=f416rawHForm 0 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) => natFourHWordFormSparse 16 (f416basis 0) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawHForm 0 b) (by decide +kernel)
  exact h 0

private theorem f416_H_source_row_1 : ∀ b : Fin 64,
    natFourHWordFormSparse 16 (f416basis 1) (f416basis b)=f416rawHForm 1 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) => natFourHWordFormSparse 16 (f416basis 1) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawHForm 1 b) (by decide +kernel)
  exact h 0

private theorem f416_H_source_row_2 : ∀ b : Fin 64,
    natFourHWordFormSparse 16 (f416basis 2) (f416basis b)=f416rawHForm 2 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) => natFourHWordFormSparse 16 (f416basis 2) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawHForm 2 b) (by decide +kernel)
  exact h 0

private theorem f416_H_source_row_3 : ∀ b : Fin 64,
    natFourHWordFormSparse 16 (f416basis 3) (f416basis b)=f416rawHForm 3 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 64) => natFourHWordFormSparse 16 (f416basis 3) (f416basis b))
    (fun (_ : Fin 1) (b : Fin 64) => f416rawHForm 3 b) (by decide +kernel)
  exact h 0

theorem f416_H_rows_0 (a b : Fin 64) (hlo : 0 ≤ a.val) (hhi : a.val < 4) :
    natFourHWordFormSparse 16 (f416basis a) (f416basis b) = f416rawHForm a b := by
  fin_cases a
  · exact f416_H_source_row_0 b
  · exact f416_H_source_row_1 b
  · exact f416_H_source_row_2 b
  · exact f416_H_source_row_3 b
  · change (4 : ℕ) < 4 at hhi
    omega
  · change (5 : ℕ) < 4 at hhi
    omega
  · change (6 : ℕ) < 4 at hhi
    omega
  · change (7 : ℕ) < 4 at hhi
    omega
  · change (8 : ℕ) < 4 at hhi
    omega
  · change (9 : ℕ) < 4 at hhi
    omega
  · change (10 : ℕ) < 4 at hhi
    omega
  · change (11 : ℕ) < 4 at hhi
    omega
  · change (12 : ℕ) < 4 at hhi
    omega
  · change (13 : ℕ) < 4 at hhi
    omega
  · change (14 : ℕ) < 4 at hhi
    omega
  · change (15 : ℕ) < 4 at hhi
    omega
  · change (16 : ℕ) < 4 at hhi
    omega
  · change (17 : ℕ) < 4 at hhi
    omega
  · change (18 : ℕ) < 4 at hhi
    omega
  · change (19 : ℕ) < 4 at hhi
    omega
  · change (20 : ℕ) < 4 at hhi
    omega
  · change (21 : ℕ) < 4 at hhi
    omega
  · change (22 : ℕ) < 4 at hhi
    omega
  · change (23 : ℕ) < 4 at hhi
    omega
  · change (24 : ℕ) < 4 at hhi
    omega
  · change (25 : ℕ) < 4 at hhi
    omega
  · change (26 : ℕ) < 4 at hhi
    omega
  · change (27 : ℕ) < 4 at hhi
    omega
  · change (28 : ℕ) < 4 at hhi
    omega
  · change (29 : ℕ) < 4 at hhi
    omega
  · change (30 : ℕ) < 4 at hhi
    omega
  · change (31 : ℕ) < 4 at hhi
    omega
  · change (32 : ℕ) < 4 at hhi
    omega
  · change (33 : ℕ) < 4 at hhi
    omega
  · change (34 : ℕ) < 4 at hhi
    omega
  · change (35 : ℕ) < 4 at hhi
    omega
  · change (36 : ℕ) < 4 at hhi
    omega
  · change (37 : ℕ) < 4 at hhi
    omega
  · change (38 : ℕ) < 4 at hhi
    omega
  · change (39 : ℕ) < 4 at hhi
    omega
  · change (40 : ℕ) < 4 at hhi
    omega
  · change (41 : ℕ) < 4 at hhi
    omega
  · change (42 : ℕ) < 4 at hhi
    omega
  · change (43 : ℕ) < 4 at hhi
    omega
  · change (44 : ℕ) < 4 at hhi
    omega
  · change (45 : ℕ) < 4 at hhi
    omega
  · change (46 : ℕ) < 4 at hhi
    omega
  · change (47 : ℕ) < 4 at hhi
    omega
  · change (48 : ℕ) < 4 at hhi
    omega
  · change (49 : ℕ) < 4 at hhi
    omega
  · change (50 : ℕ) < 4 at hhi
    omega
  · change (51 : ℕ) < 4 at hhi
    omega
  · change (52 : ℕ) < 4 at hhi
    omega
  · change (53 : ℕ) < 4 at hhi
    omega
  · change (54 : ℕ) < 4 at hhi
    omega
  · change (55 : ℕ) < 4 at hhi
    omega
  · change (56 : ℕ) < 4 at hhi
    omega
  · change (57 : ℕ) < 4 at hhi
    omega
  · change (58 : ℕ) < 4 at hhi
    omega
  · change (59 : ℕ) < 4 at hhi
    omega
  · change (60 : ℕ) < 4 at hhi
    omega
  · change (61 : ℕ) < 4 at hhi
    omega
  · change (62 : ℕ) < 4 at hhi
    omega
  · change (63 : ℕ) < 4 at hhi
    omega

#print axioms f416_H_rows_0
end TorusLean.BosonFiniteCertificate
