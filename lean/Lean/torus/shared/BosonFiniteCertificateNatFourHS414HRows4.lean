import torus.shared.BosonFiniteCertificateNatFourHS414Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f414_H_source_row_24 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 24) (f414basis b)=f414rawHForm 24 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 24) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 24 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_25 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 25) (f414basis b)=f414rawHForm 25 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 25) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 25 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_26 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 26) (f414basis b)=f414rawHForm 26 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 26) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 26 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_27 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 27) (f414basis b)=f414rawHForm 27 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 27) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 27 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_28 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 28) (f414basis b)=f414rawHForm 28 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 28) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 28 b) (by decide +kernel)
  exact h 0

private theorem f414_H_source_row_29 : ∀ b : Fin 47,
    natFourHWordFormSparse 14 (f414basis 29) (f414basis b)=f414rawHForm 29 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 47) => natFourHWordFormSparse 14 (f414basis 29) (f414basis b))
    (fun (_ : Fin 1) (b : Fin 47) => f414rawHForm 29 b) (by decide +kernel)
  exact h 0

theorem f414_H_rows_4 (a b : Fin 47) (hlo : 24 ≤ a.val) (hhi : a.val < 30) :
    natFourHWordFormSparse 14 (f414basis a) (f414basis b) = f414rawHForm a b := by
  fin_cases a
  · change 24 ≤ (0 : ℕ) at hlo
    omega
  · change 24 ≤ (1 : ℕ) at hlo
    omega
  · change 24 ≤ (2 : ℕ) at hlo
    omega
  · change 24 ≤ (3 : ℕ) at hlo
    omega
  · change 24 ≤ (4 : ℕ) at hlo
    omega
  · change 24 ≤ (5 : ℕ) at hlo
    omega
  · change 24 ≤ (6 : ℕ) at hlo
    omega
  · change 24 ≤ (7 : ℕ) at hlo
    omega
  · change 24 ≤ (8 : ℕ) at hlo
    omega
  · change 24 ≤ (9 : ℕ) at hlo
    omega
  · change 24 ≤ (10 : ℕ) at hlo
    omega
  · change 24 ≤ (11 : ℕ) at hlo
    omega
  · change 24 ≤ (12 : ℕ) at hlo
    omega
  · change 24 ≤ (13 : ℕ) at hlo
    omega
  · change 24 ≤ (14 : ℕ) at hlo
    omega
  · change 24 ≤ (15 : ℕ) at hlo
    omega
  · change 24 ≤ (16 : ℕ) at hlo
    omega
  · change 24 ≤ (17 : ℕ) at hlo
    omega
  · change 24 ≤ (18 : ℕ) at hlo
    omega
  · change 24 ≤ (19 : ℕ) at hlo
    omega
  · change 24 ≤ (20 : ℕ) at hlo
    omega
  · change 24 ≤ (21 : ℕ) at hlo
    omega
  · change 24 ≤ (22 : ℕ) at hlo
    omega
  · change 24 ≤ (23 : ℕ) at hlo
    omega
  · exact f414_H_source_row_24 b
  · exact f414_H_source_row_25 b
  · exact f414_H_source_row_26 b
  · exact f414_H_source_row_27 b
  · exact f414_H_source_row_28 b
  · exact f414_H_source_row_29 b
  · change (30 : ℕ) < 30 at hhi
    omega
  · change (31 : ℕ) < 30 at hhi
    omega
  · change (32 : ℕ) < 30 at hhi
    omega
  · change (33 : ℕ) < 30 at hhi
    omega
  · change (34 : ℕ) < 30 at hhi
    omega
  · change (35 : ℕ) < 30 at hhi
    omega
  · change (36 : ℕ) < 30 at hhi
    omega
  · change (37 : ℕ) < 30 at hhi
    omega
  · change (38 : ℕ) < 30 at hhi
    omega
  · change (39 : ℕ) < 30 at hhi
    omega
  · change (40 : ℕ) < 30 at hhi
    omega
  · change (41 : ℕ) < 30 at hhi
    omega
  · change (42 : ℕ) < 30 at hhi
    omega
  · change (43 : ℕ) < 30 at hhi
    omega
  · change (44 : ℕ) < 30 at hhi
    omega
  · change (45 : ℕ) < 30 at hhi
    omega
  · change (46 : ℕ) < 30 at hhi
    omega

#print axioms f414_H_rows_4
end TorusLean.BosonFiniteCertificate
