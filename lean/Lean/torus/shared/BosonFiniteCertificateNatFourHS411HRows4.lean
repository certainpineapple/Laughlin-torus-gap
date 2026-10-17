import torus.shared.BosonFiniteCertificateNatFourHS411Data
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

private theorem f411_H_source_row_24 : ∀ b : Fin 27,
    natFourHWordFormSparse 11 (f411basis 24) (f411basis b)=f411rawHForm 24 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 27) => natFourHWordFormSparse 11 (f411basis 24) (f411basis b))
    (fun (_ : Fin 1) (b : Fin 27) => f411rawHForm 24 b) (by decide +kernel)
  exact h 0

private theorem f411_H_source_row_25 : ∀ b : Fin 27,
    natFourHWordFormSparse 11 (f411basis 25) (f411basis b)=f411rawHForm 25 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 27) => natFourHWordFormSparse 11 (f411basis 25) (f411basis b))
    (fun (_ : Fin 1) (b : Fin 27) => f411rawHForm 25 b) (by decide +kernel)
  exact h 0

private theorem f411_H_source_row_26 : ∀ b : Fin 27,
    natFourHWordFormSparse 11 (f411basis 26) (f411basis b)=f411rawHForm 26 b := by
  have h := natFourRationalEntryCheck_sound
    (fun (_ : Fin 1) (b : Fin 27) => natFourHWordFormSparse 11 (f411basis 26) (f411basis b))
    (fun (_ : Fin 1) (b : Fin 27) => f411rawHForm 26 b) (by decide +kernel)
  exact h 0

theorem f411_H_rows_4 (a b : Fin 27) (hlo : 24 ≤ a.val) (hhi : a.val < 27) :
    natFourHWordFormSparse 11 (f411basis a) (f411basis b) = f411rawHForm a b := by
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
  · exact f411_H_source_row_24 b
  · exact f411_H_source_row_25 b
  · exact f411_H_source_row_26 b

#print axioms f411_H_rows_4
end TorusLean.BosonFiniteCertificate
