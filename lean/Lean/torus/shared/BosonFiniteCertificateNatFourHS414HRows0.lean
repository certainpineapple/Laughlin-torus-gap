import torus.shared.BosonFiniteCertificateNatFourHS414Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f414_H_source_row_0 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 0) (f414basis b)=f414rawHForm 0 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 0) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 0 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_1 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 1) (f414basis b)=f414rawHForm 1 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 1) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 1 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_2 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 2) (f414basis b)=f414rawHForm 2 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 2) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 2 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_3 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 3) (f414basis b)=f414rawHForm 3 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 3) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 3 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_4 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 4) (f414basis b)=f414rawHForm 4 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 4) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 4 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_5 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 5) (f414basis b)=f414rawHForm 5 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 5) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 5 b) (by decide +kernel)
  exact h 0

theorem f414_H_rows_0 (a b : Fin 47) (hlo : 0 ≤ a.val) (hhi : a.val < 6) :
    natFourHWordFormSparse 14 (f414basis a) (f414basis b) = f414rawHForm a b := by
  fin_cases a
  · exact f414_H_source_row_0 b
  · exact f414_H_source_row_1 b
  · exact f414_H_source_row_2 b
  · exact f414_H_source_row_3 b
  · exact f414_H_source_row_4 b
  · exact f414_H_source_row_5 b
  · change (6 : ℕ) < 6 at hhi
    omega
  · change (7 : ℕ) < 6 at hhi
    omega
  · change (8 : ℕ) < 6 at hhi
    omega
  · change (9 : ℕ) < 6 at hhi
    omega
  · change (10 : ℕ) < 6 at hhi
    omega
  · change (11 : ℕ) < 6 at hhi
    omega
  · change (12 : ℕ) < 6 at hhi
    omega
  · change (13 : ℕ) < 6 at hhi
    omega
  · change (14 : ℕ) < 6 at hhi
    omega
  · change (15 : ℕ) < 6 at hhi
    omega
  · change (16 : ℕ) < 6 at hhi
    omega
  · change (17 : ℕ) < 6 at hhi
    omega
  · change (18 : ℕ) < 6 at hhi
    omega
  · change (19 : ℕ) < 6 at hhi
    omega
  · change (20 : ℕ) < 6 at hhi
    omega
  · change (21 : ℕ) < 6 at hhi
    omega
  · change (22 : ℕ) < 6 at hhi
    omega
  · change (23 : ℕ) < 6 at hhi
    omega
  · change (24 : ℕ) < 6 at hhi
    omega
  · change (25 : ℕ) < 6 at hhi
    omega
  · change (26 : ℕ) < 6 at hhi
    omega
  · change (27 : ℕ) < 6 at hhi
    omega
  · change (28 : ℕ) < 6 at hhi
    omega
  · change (29 : ℕ) < 6 at hhi
    omega
  · change (30 : ℕ) < 6 at hhi
    omega
  · change (31 : ℕ) < 6 at hhi
    omega
  · change (32 : ℕ) < 6 at hhi
    omega
  · change (33 : ℕ) < 6 at hhi
    omega
  · change (34 : ℕ) < 6 at hhi
    omega
  · change (35 : ℕ) < 6 at hhi
    omega
  · change (36 : ℕ) < 6 at hhi
    omega
  · change (37 : ℕ) < 6 at hhi
    omega
  · change (38 : ℕ) < 6 at hhi
    omega
  · change (39 : ℕ) < 6 at hhi
    omega
  · change (40 : ℕ) < 6 at hhi
    omega
  · change (41 : ℕ) < 6 at hhi
    omega
  · change (42 : ℕ) < 6 at hhi
    omega
  · change (43 : ℕ) < 6 at hhi
    omega
  · change (44 : ℕ) < 6 at hhi
    omega
  · change (45 : ℕ) < 6 at hhi
    omega
  · change (46 : ℕ) < 6 at hhi
    omega

#print axioms f414_H_rows_0
end TorusLean.BosonFiniteCertificate
