import torus.shared.BosonFiniteCertificateNatFourHS411Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f411_H_source_row_18 : ∀ b : Fin 27,
    natFourHWordFormSparse 11 (f411basis 18) (f411basis b)=f411rawHForm 18 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 27) => natFourHWordFormSparse 11 (f411basis 18) (f411basis b))
    (fun (_ : Fin 1) (b : Fin 27) => f411rawHForm 18 b) (by decide +kernel)
  exact h 0

private theorem f411_H_source_row_19 : ∀ b : Fin 27,
    natFourHWordFormSparse 11 (f411basis 19) (f411basis b)=f411rawHForm 19 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 27) => natFourHWordFormSparse 11 (f411basis 19) (f411basis b))
    (fun (_ : Fin 1) (b : Fin 27) => f411rawHForm 19 b) (by decide +kernel)
  exact h 0

private theorem f411_H_source_row_20 : ∀ b : Fin 27,
    natFourHWordFormSparse 11 (f411basis 20) (f411basis b)=f411rawHForm 20 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 27) => natFourHWordFormSparse 11 (f411basis 20) (f411basis b))
    (fun (_ : Fin 1) (b : Fin 27) => f411rawHForm 20 b) (by decide +kernel)
  exact h 0

private theorem f411_H_source_row_21 : ∀ b : Fin 27,
    natFourHWordFormSparse 11 (f411basis 21) (f411basis b)=f411rawHForm 21 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 27) => natFourHWordFormSparse 11 (f411basis 21) (f411basis b))
    (fun (_ : Fin 1) (b : Fin 27) => f411rawHForm 21 b) (by decide +kernel)
  exact h 0

private theorem f411_H_source_row_22 : ∀ b : Fin 27,
    natFourHWordFormSparse 11 (f411basis 22) (f411basis b)=f411rawHForm 22 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 27) => natFourHWordFormSparse 11 (f411basis 22) (f411basis b))
    (fun (_ : Fin 1) (b : Fin 27) => f411rawHForm 22 b) (by decide +kernel)
  exact h 0

private theorem f411_H_source_row_23 : ∀ b : Fin 27,
    natFourHWordFormSparse 11 (f411basis 23) (f411basis b)=f411rawHForm 23 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 27) => natFourHWordFormSparse 11 (f411basis 23) (f411basis b))
    (fun (_ : Fin 1) (b : Fin 27) => f411rawHForm 23 b) (by decide +kernel)
  exact h 0

theorem f411_H_rows_3 (a b : Fin 27) (hlo : 18 ≤ a.val) (hhi : a.val < 24) :
    natFourHWordFormSparse 11 (f411basis a) (f411basis b) = f411rawHForm a b := by
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
  · exact f411_H_source_row_18 b
  · exact f411_H_source_row_19 b
  · exact f411_H_source_row_20 b
  · exact f411_H_source_row_21 b
  · exact f411_H_source_row_22 b
  · exact f411_H_source_row_23 b
  · change (24 : ℕ) < 24 at hhi
    omega
  · change (25 : ℕ) < 24 at hhi
    omega
  · change (26 : ℕ) < 24 at hhi
    omega

#print axioms f411_H_rows_3
end TorusLean.BosonFiniteCertificate
