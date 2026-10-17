import torus.shared.BosonFiniteCertificateNatFourHS414Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f414_H_source_row_30 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 30) (f414basis b)=f414rawHForm 30 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 30) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 30 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_31 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 31) (f414basis b)=f414rawHForm 31 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 31) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 31 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_32 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 32) (f414basis b)=f414rawHForm 32 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 32) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 32 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_33 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 33) (f414basis b)=f414rawHForm 33 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 33) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 33 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_34 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 34) (f414basis b)=f414rawHForm 34 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 34) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 34 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_35 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 35) (f414basis b)=f414rawHForm 35 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 35) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 35 b) (by decide +kernel)
  exact h 0

theorem f414_H_rows_5 (a b : Fin 47) (hlo : 30 ≤ a.val) (hhi : a.val < 36) :
    natFourHWordFormSparse 14 (f414basis a) (f414basis b) = f414rawHForm a b := by
  fin_cases a
  · change 30 ≤ (0 : ℕ) at hlo
    omega
  · change 30 ≤ (1 : ℕ) at hlo
    omega
  · change 30 ≤ (2 : ℕ) at hlo
    omega
  · change 30 ≤ (3 : ℕ) at hlo
    omega
  · change 30 ≤ (4 : ℕ) at hlo
    omega
  · change 30 ≤ (5 : ℕ) at hlo
    omega
  · change 30 ≤ (6 : ℕ) at hlo
    omega
  · change 30 ≤ (7 : ℕ) at hlo
    omega
  · change 30 ≤ (8 : ℕ) at hlo
    omega
  · change 30 ≤ (9 : ℕ) at hlo
    omega
  · change 30 ≤ (10 : ℕ) at hlo
    omega
  · change 30 ≤ (11 : ℕ) at hlo
    omega
  · change 30 ≤ (12 : ℕ) at hlo
    omega
  · change 30 ≤ (13 : ℕ) at hlo
    omega
  · change 30 ≤ (14 : ℕ) at hlo
    omega
  · change 30 ≤ (15 : ℕ) at hlo
    omega
  · change 30 ≤ (16 : ℕ) at hlo
    omega
  · change 30 ≤ (17 : ℕ) at hlo
    omega
  · change 30 ≤ (18 : ℕ) at hlo
    omega
  · change 30 ≤ (19 : ℕ) at hlo
    omega
  · change 30 ≤ (20 : ℕ) at hlo
    omega
  · change 30 ≤ (21 : ℕ) at hlo
    omega
  · change 30 ≤ (22 : ℕ) at hlo
    omega
  · change 30 ≤ (23 : ℕ) at hlo
    omega
  · change 30 ≤ (24 : ℕ) at hlo
    omega
  · change 30 ≤ (25 : ℕ) at hlo
    omega
  · change 30 ≤ (26 : ℕ) at hlo
    omega
  · change 30 ≤ (27 : ℕ) at hlo
    omega
  · change 30 ≤ (28 : ℕ) at hlo
    omega
  · change 30 ≤ (29 : ℕ) at hlo
    omega
  · exact f414_H_source_row_30 b
  · exact f414_H_source_row_31 b
  · exact f414_H_source_row_32 b
  · exact f414_H_source_row_33 b
  · exact f414_H_source_row_34 b
  · exact f414_H_source_row_35 b
  · change (36 : ℕ) < 36 at hhi
    omega
  · change (37 : ℕ) < 36 at hhi
    omega
  · change (38 : ℕ) < 36 at hhi
    omega
  · change (39 : ℕ) < 36 at hhi
    omega
  · change (40 : ℕ) < 36 at hhi
    omega
  · change (41 : ℕ) < 36 at hhi
    omega
  · change (42 : ℕ) < 36 at hhi
    omega
  · change (43 : ℕ) < 36 at hhi
    omega
  · change (44 : ℕ) < 36 at hhi
    omega
  · change (45 : ℕ) < 36 at hhi
    omega
  · change (46 : ℕ) < 36 at hhi
    omega

#print axioms f414_H_rows_5
end TorusLean.BosonFiniteCertificate
