import torus.shared.BosonFiniteCertificateNatFourHS410Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f410_H_source_row_18 : ∀ b : Fin 23,
    natFourHWordFormSparse 10 (f410basis 18) (f410basis b)=f410rawHForm 18 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 23) => natFourHWordFormSparse 10 (f410basis 18) (f410basis b))
    (fun (_ : Fin 1) (b : Fin 23) => f410rawHForm 18 b) (by decide +kernel)
  exact h 0

private theorem f410_H_source_row_19 : ∀ b : Fin 23,
    natFourHWordFormSparse 10 (f410basis 19) (f410basis b)=f410rawHForm 19 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 23) => natFourHWordFormSparse 10 (f410basis 19) (f410basis b))
    (fun (_ : Fin 1) (b : Fin 23) => f410rawHForm 19 b) (by decide +kernel)
  exact h 0

private theorem f410_H_source_row_20 : ∀ b : Fin 23,
    natFourHWordFormSparse 10 (f410basis 20) (f410basis b)=f410rawHForm 20 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 23) => natFourHWordFormSparse 10 (f410basis 20) (f410basis b))
    (fun (_ : Fin 1) (b : Fin 23) => f410rawHForm 20 b) (by decide +kernel)
  exact h 0

private theorem f410_H_source_row_21 : ∀ b : Fin 23,
    natFourHWordFormSparse 10 (f410basis 21) (f410basis b)=f410rawHForm 21 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 23) => natFourHWordFormSparse 10 (f410basis 21) (f410basis b))
    (fun (_ : Fin 1) (b : Fin 23) => f410rawHForm 21 b) (by decide +kernel)
  exact h 0

private theorem f410_H_source_row_22 : ∀ b : Fin 23,
    natFourHWordFormSparse 10 (f410basis 22) (f410basis b)=f410rawHForm 22 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 23) => natFourHWordFormSparse 10 (f410basis 22) (f410basis b))
    (fun (_ : Fin 1) (b : Fin 23) => f410rawHForm 22 b) (by decide +kernel)
  exact h 0

theorem f410_H_rows_3 (a b : Fin 23) (hlo : 18 ≤ a.val) (hhi : a.val < 23) :
    natFourHWordFormSparse 10 (f410basis a) (f410basis b) = f410rawHForm a b := by
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
  · exact f410_H_source_row_18 b
  · exact f410_H_source_row_19 b
  · exact f410_H_source_row_20 b
  · exact f410_H_source_row_21 b
  · exact f410_H_source_row_22 b

#print axioms f410_H_rows_3
end TorusLean.BosonFiniteCertificate
