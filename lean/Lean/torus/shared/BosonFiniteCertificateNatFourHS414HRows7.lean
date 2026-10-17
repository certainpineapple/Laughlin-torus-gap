import torus.shared.BosonFiniteCertificateNatFourHS414Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f414_H_source_row_42 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 42) (f414basis b)=f414rawHForm 42 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 42) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 42 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_43 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 43) (f414basis b)=f414rawHForm 43 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 43) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 43 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_44 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 44) (f414basis b)=f414rawHForm 44 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 44) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 44 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_45 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 45) (f414basis b)=f414rawHForm 45 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 45) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 45 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_46 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 46) (f414basis b)=f414rawHForm 46 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 46) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 46 b) (by decide +kernel)
  exact h 0

theorem f414_H_rows_7 (a b : Fin 47) (hlo : 42 ≤ a.val) (hhi : a.val < 47) :
    natFourHWordFormSparse 14 (f414basis a) (f414basis b) = f414rawHForm a b := by
  fin_cases a
  · change 42 ≤ (0 : ℕ) at hlo
    omega
  · change 42 ≤ (1 : ℕ) at hlo
    omega
  · change 42 ≤ (2 : ℕ) at hlo
    omega
  · change 42 ≤ (3 : ℕ) at hlo
    omega
  · change 42 ≤ (4 : ℕ) at hlo
    omega
  · change 42 ≤ (5 : ℕ) at hlo
    omega
  · change 42 ≤ (6 : ℕ) at hlo
    omega
  · change 42 ≤ (7 : ℕ) at hlo
    omega
  · change 42 ≤ (8 : ℕ) at hlo
    omega
  · change 42 ≤ (9 : ℕ) at hlo
    omega
  · change 42 ≤ (10 : ℕ) at hlo
    omega
  · change 42 ≤ (11 : ℕ) at hlo
    omega
  · change 42 ≤ (12 : ℕ) at hlo
    omega
  · change 42 ≤ (13 : ℕ) at hlo
    omega
  · change 42 ≤ (14 : ℕ) at hlo
    omega
  · change 42 ≤ (15 : ℕ) at hlo
    omega
  · change 42 ≤ (16 : ℕ) at hlo
    omega
  · change 42 ≤ (17 : ℕ) at hlo
    omega
  · change 42 ≤ (18 : ℕ) at hlo
    omega
  · change 42 ≤ (19 : ℕ) at hlo
    omega
  · change 42 ≤ (20 : ℕ) at hlo
    omega
  · change 42 ≤ (21 : ℕ) at hlo
    omega
  · change 42 ≤ (22 : ℕ) at hlo
    omega
  · change 42 ≤ (23 : ℕ) at hlo
    omega
  · change 42 ≤ (24 : ℕ) at hlo
    omega
  · change 42 ≤ (25 : ℕ) at hlo
    omega
  · change 42 ≤ (26 : ℕ) at hlo
    omega
  · change 42 ≤ (27 : ℕ) at hlo
    omega
  · change 42 ≤ (28 : ℕ) at hlo
    omega
  · change 42 ≤ (29 : ℕ) at hlo
    omega
  · change 42 ≤ (30 : ℕ) at hlo
    omega
  · change 42 ≤ (31 : ℕ) at hlo
    omega
  · change 42 ≤ (32 : ℕ) at hlo
    omega
  · change 42 ≤ (33 : ℕ) at hlo
    omega
  · change 42 ≤ (34 : ℕ) at hlo
    omega
  · change 42 ≤ (35 : ℕ) at hlo
    omega
  · change 42 ≤ (36 : ℕ) at hlo
    omega
  · change 42 ≤ (37 : ℕ) at hlo
    omega
  · change 42 ≤ (38 : ℕ) at hlo
    omega
  · change 42 ≤ (39 : ℕ) at hlo
    omega
  · change 42 ≤ (40 : ℕ) at hlo
    omega
  · change 42 ≤ (41 : ℕ) at hlo
    omega
  · exact f414_H_source_row_42 b
  · exact f414_H_source_row_43 b
  · exact f414_H_source_row_44 b
  · exact f414_H_source_row_45 b
  · exact f414_H_source_row_46 b

#print axioms f414_H_rows_7
end TorusLean.BosonFiniteCertificate
