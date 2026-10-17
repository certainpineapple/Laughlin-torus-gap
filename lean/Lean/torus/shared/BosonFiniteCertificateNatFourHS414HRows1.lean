import torus.shared.BosonFiniteCertificateNatFourHS414Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f414_H_source_row_6 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 6) (f414basis b)=f414rawHForm 6 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 6) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 6 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_7 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 7) (f414basis b)=f414rawHForm 7 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 7) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 7 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_8 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 8) (f414basis b)=f414rawHForm 8 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 8) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 8 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_9 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 9) (f414basis b)=f414rawHForm 9 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 9) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 9 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_10 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 10) (f414basis b)=f414rawHForm 10 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 10) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 10 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_11 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 11) (f414basis b)=f414rawHForm 11 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 11) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 11 b) (by decide +kernel)
  exact h 0

theorem f414_H_rows_1 (a b : Fin 47) (hlo : 6 ≤ a.val) (hhi : a.val < 12) :
    natFourHWordFormSparse 14 (f414basis a) (f414basis b) = f414rawHForm a b := by
  fin_cases a
  · change 6 ≤ (0 : ℕ) at hlo
    omega
  · change 6 ≤ (1 : ℕ) at hlo
    omega
  · change 6 ≤ (2 : ℕ) at hlo
    omega
  · change 6 ≤ (3 : ℕ) at hlo
    omega
  · change 6 ≤ (4 : ℕ) at hlo
    omega
  · change 6 ≤ (5 : ℕ) at hlo
    omega
  · exact f414_H_source_row_6 b
  · exact f414_H_source_row_7 b
  · exact f414_H_source_row_8 b
  · exact f414_H_source_row_9 b
  · exact f414_H_source_row_10 b
  · exact f414_H_source_row_11 b
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

#print axioms f414_H_rows_1
end TorusLean.BosonFiniteCertificate
