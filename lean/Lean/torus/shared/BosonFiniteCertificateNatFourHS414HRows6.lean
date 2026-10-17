import torus.shared.BosonFiniteCertificateNatFourHS414Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f414_H_source_row_36 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 36) (f414basis b)=f414rawHForm 36 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 36) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 36 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_37 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 37) (f414basis b)=f414rawHForm 37 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 37) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 37 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_38 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 38) (f414basis b)=f414rawHForm 38 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 38) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 38 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_39 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 39) (f414basis b)=f414rawHForm 39 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 39) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 39 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_40 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 40) (f414basis b)=f414rawHForm 40 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 40) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 40 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_41 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 41) (f414basis b)=f414rawHForm 41 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 41) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 41 b) (by decide +kernel)
  exact h 0

theorem f414_H_rows_6 (a b : Fin 47) (hlo : 36 ≤ a.val) (hhi : a.val < 42) :
    natFourHWordFormSparse 14 (f414basis a) (f414basis b) = f414rawHForm a b := by
  fin_cases a
  · change 36 ≤ (0 : ℕ) at hlo
    omega
  · change 36 ≤ (1 : ℕ) at hlo
    omega
  · change 36 ≤ (2 : ℕ) at hlo
    omega
  · change 36 ≤ (3 : ℕ) at hlo
    omega
  · change 36 ≤ (4 : ℕ) at hlo
    omega
  · change 36 ≤ (5 : ℕ) at hlo
    omega
  · change 36 ≤ (6 : ℕ) at hlo
    omega
  · change 36 ≤ (7 : ℕ) at hlo
    omega
  · change 36 ≤ (8 : ℕ) at hlo
    omega
  · change 36 ≤ (9 : ℕ) at hlo
    omega
  · change 36 ≤ (10 : ℕ) at hlo
    omega
  · change 36 ≤ (11 : ℕ) at hlo
    omega
  · change 36 ≤ (12 : ℕ) at hlo
    omega
  · change 36 ≤ (13 : ℕ) at hlo
    omega
  · change 36 ≤ (14 : ℕ) at hlo
    omega
  · change 36 ≤ (15 : ℕ) at hlo
    omega
  · change 36 ≤ (16 : ℕ) at hlo
    omega
  · change 36 ≤ (17 : ℕ) at hlo
    omega
  · change 36 ≤ (18 : ℕ) at hlo
    omega
  · change 36 ≤ (19 : ℕ) at hlo
    omega
  · change 36 ≤ (20 : ℕ) at hlo
    omega
  · change 36 ≤ (21 : ℕ) at hlo
    omega
  · change 36 ≤ (22 : ℕ) at hlo
    omega
  · change 36 ≤ (23 : ℕ) at hlo
    omega
  · change 36 ≤ (24 : ℕ) at hlo
    omega
  · change 36 ≤ (25 : ℕ) at hlo
    omega
  · change 36 ≤ (26 : ℕ) at hlo
    omega
  · change 36 ≤ (27 : ℕ) at hlo
    omega
  · change 36 ≤ (28 : ℕ) at hlo
    omega
  · change 36 ≤ (29 : ℕ) at hlo
    omega
  · change 36 ≤ (30 : ℕ) at hlo
    omega
  · change 36 ≤ (31 : ℕ) at hlo
    omega
  · change 36 ≤ (32 : ℕ) at hlo
    omega
  · change 36 ≤ (33 : ℕ) at hlo
    omega
  · change 36 ≤ (34 : ℕ) at hlo
    omega
  · change 36 ≤ (35 : ℕ) at hlo
    omega
  · exact f414_H_source_row_36 b
  · exact f414_H_source_row_37 b
  · exact f414_H_source_row_38 b
  · exact f414_H_source_row_39 b
  · exact f414_H_source_row_40 b
  · exact f414_H_source_row_41 b
  · change (42 : ℕ) < 42 at hhi
    omega
  · change (43 : ℕ) < 42 at hhi
    omega
  · change (44 : ℕ) < 42 at hhi
    omega
  · change (45 : ℕ) < 42 at hhi
    omega
  · change (46 : ℕ) < 42 at hhi
    omega

#print axioms f414_H_rows_6
end TorusLean.BosonFiniteCertificate
