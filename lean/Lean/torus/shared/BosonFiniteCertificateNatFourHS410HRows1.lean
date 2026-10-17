import torus.shared.BosonFiniteCertificateNatFourHS410Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f410_H_source_row_6 : ∀ b : Fin 23,
    natFourHWordFormSparse 10 (f410basis 6) (f410basis b)=f410rawHForm 6 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 23) => natFourHWordFormSparse 10 (f410basis 6) (f410basis b))
    (fun (_ : Fin 1) (b : Fin 23) => f410rawHForm 6 b) (by decide +kernel)
  exact h 0

private theorem f410_H_source_row_7 : ∀ b : Fin 23,
    natFourHWordFormSparse 10 (f410basis 7) (f410basis b)=f410rawHForm 7 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 23) => natFourHWordFormSparse 10 (f410basis 7) (f410basis b))
    (fun (_ : Fin 1) (b : Fin 23) => f410rawHForm 7 b) (by decide +kernel)
  exact h 0

private theorem f410_H_source_row_8 : ∀ b : Fin 23,
    natFourHWordFormSparse 10 (f410basis 8) (f410basis b)=f410rawHForm 8 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 23) => natFourHWordFormSparse 10 (f410basis 8) (f410basis b))
    (fun (_ : Fin 1) (b : Fin 23) => f410rawHForm 8 b) (by decide +kernel)
  exact h 0

private theorem f410_H_source_row_9 : ∀ b : Fin 23,
    natFourHWordFormSparse 10 (f410basis 9) (f410basis b)=f410rawHForm 9 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 23) => natFourHWordFormSparse 10 (f410basis 9) (f410basis b))
    (fun (_ : Fin 1) (b : Fin 23) => f410rawHForm 9 b) (by decide +kernel)
  exact h 0

private theorem f410_H_source_row_10 : ∀ b : Fin 23,
    natFourHWordFormSparse 10 (f410basis 10) (f410basis b)=f410rawHForm 10 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 23) => natFourHWordFormSparse 10 (f410basis 10) (f410basis b))
    (fun (_ : Fin 1) (b : Fin 23) => f410rawHForm 10 b) (by decide +kernel)
  exact h 0

private theorem f410_H_source_row_11 : ∀ b : Fin 23,
    natFourHWordFormSparse 10 (f410basis 11) (f410basis b)=f410rawHForm 11 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 23) => natFourHWordFormSparse 10 (f410basis 11) (f410basis b))
    (fun (_ : Fin 1) (b : Fin 23) => f410rawHForm 11 b) (by decide +kernel)
  exact h 0

theorem f410_H_rows_1 (a b : Fin 23) (hlo : 6 ≤ a.val) (hhi : a.val < 12) :
    natFourHWordFormSparse 10 (f410basis a) (f410basis b) = f410rawHForm a b := by
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
  · exact f410_H_source_row_6 b
  · exact f410_H_source_row_7 b
  · exact f410_H_source_row_8 b
  · exact f410_H_source_row_9 b
  · exact f410_H_source_row_10 b
  · exact f410_H_source_row_11 b
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

#print axioms f410_H_rows_1
end TorusLean.BosonFiniteCertificate
