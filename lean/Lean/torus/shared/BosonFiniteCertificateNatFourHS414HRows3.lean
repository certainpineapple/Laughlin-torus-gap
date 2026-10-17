import torus.shared.BosonFiniteCertificateNatFourHS414Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f414_H_source_row_18 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 18) (f414basis b)=f414rawHForm 18 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 18) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 18 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_19 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 19) (f414basis b)=f414rawHForm 19 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 19) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 19 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_20 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 20) (f414basis b)=f414rawHForm 20 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 20) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 20 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_21 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 21) (f414basis b)=f414rawHForm 21 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 21) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 21 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_22 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 22) (f414basis b)=f414rawHForm 22 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 22) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 22 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_23 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 23) (f414basis b)=f414rawHForm 23 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 23) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 23 b) (by decide +kernel)
  exact h 0

theorem f414_H_rows_3 (a b : Fin 47) (hlo : 18 ≤ a.val) (hhi : a.val < 24) :
    natFourHWordFormSparse 14 (f414basis a) (f414basis b) = f414rawHForm a b := by
  fin_cases a
  · change 18 ≤ (0 : ℕ) at hlo
    omega
  · change 18 ≤ (1 : ℕ) at hlo
    omega
  · change 18 ≤ (2 : ℕ) at hlo
    omega
  · change 18 ≤ (3 : ℕ) at hlo
    omega
  · change 18 ≤ (4 : ℕ) at hlo
    omega
  · change 18 ≤ (5 : ℕ) at hlo
    omega
  · change 18 ≤ (6 : ℕ) at hlo
    omega
  · change 18 ≤ (7 : ℕ) at hlo
    omega
  · change 18 ≤ (8 : ℕ) at hlo
    omega
  · change 18 ≤ (9 : ℕ) at hlo
    omega
  · change 18 ≤ (10 : ℕ) at hlo
    omega
  · change 18 ≤ (11 : ℕ) at hlo
    omega
  · change 18 ≤ (12 : ℕ) at hlo
    omega
  · change 18 ≤ (13 : ℕ) at hlo
    omega
  · change 18 ≤ (14 : ℕ) at hlo
    omega
  · change 18 ≤ (15 : ℕ) at hlo
    omega
  · change 18 ≤ (16 : ℕ) at hlo
    omega
  · change 18 ≤ (17 : ℕ) at hlo
    omega
  · exact f414_H_source_row_18 b
  · exact f414_H_source_row_19 b
  · exact f414_H_source_row_20 b
  · exact f414_H_source_row_21 b
  · exact f414_H_source_row_22 b
  · exact f414_H_source_row_23 b
  · change (24 : ℕ) < 24 at hhi
    omega
  · change (25 : ℕ) < 24 at hhi
    omega
  · change (26 : ℕ) < 24 at hhi
    omega
  · change (27 : ℕ) < 24 at hhi
    omega
  · change (28 : ℕ) < 24 at hhi
    omega
  · change (29 : ℕ) < 24 at hhi
    omega
  · change (30 : ℕ) < 24 at hhi
    omega
  · change (31 : ℕ) < 24 at hhi
    omega
  · change (32 : ℕ) < 24 at hhi
    omega
  · change (33 : ℕ) < 24 at hhi
    omega
  · change (34 : ℕ) < 24 at hhi
    omega
  · change (35 : ℕ) < 24 at hhi
    omega
  · change (36 : ℕ) < 24 at hhi
    omega
  · change (37 : ℕ) < 24 at hhi
    omega
  · change (38 : ℕ) < 24 at hhi
    omega
  · change (39 : ℕ) < 24 at hhi
    omega
  · change (40 : ℕ) < 24 at hhi
    omega
  · change (41 : ℕ) < 24 at hhi
    omega
  · change (42 : ℕ) < 24 at hhi
    omega
  · change (43 : ℕ) < 24 at hhi
    omega
  · change (44 : ℕ) < 24 at hhi
    omega
  · change (45 : ℕ) < 24 at hhi
    omega
  · change (46 : ℕ) < 24 at hhi
    omega

#print axioms f414_H_rows_3
end TorusLean.BosonFiniteCertificate
