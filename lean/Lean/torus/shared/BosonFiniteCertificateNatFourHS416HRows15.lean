import torus.shared.BosonFiniteCertificateNatFourHS416HRows15Half0
import torus.shared.BosonFiniteCertificateNatFourHS416HRows15Half1
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

theorem f416_H_rows_15 (a b : Fin 64) (hlo : 60 ≤ a.val) (hhi : a.val < 64) :
    natFourHWordFormSparse 16 (f416basis a) (f416basis b) = f416rawHForm a b := by
  fin_cases a
  · change 60 ≤ (0 : ℕ) at hlo
    omega
  · change 60 ≤ (1 : ℕ) at hlo
    omega
  · change 60 ≤ (2 : ℕ) at hlo
    omega
  · change 60 ≤ (3 : ℕ) at hlo
    omega
  · change 60 ≤ (4 : ℕ) at hlo
    omega
  · change 60 ≤ (5 : ℕ) at hlo
    omega
  · change 60 ≤ (6 : ℕ) at hlo
    omega
  · change 60 ≤ (7 : ℕ) at hlo
    omega
  · change 60 ≤ (8 : ℕ) at hlo
    omega
  · change 60 ≤ (9 : ℕ) at hlo
    omega
  · change 60 ≤ (10 : ℕ) at hlo
    omega
  · change 60 ≤ (11 : ℕ) at hlo
    omega
  · change 60 ≤ (12 : ℕ) at hlo
    omega
  · change 60 ≤ (13 : ℕ) at hlo
    omega
  · change 60 ≤ (14 : ℕ) at hlo
    omega
  · change 60 ≤ (15 : ℕ) at hlo
    omega
  · change 60 ≤ (16 : ℕ) at hlo
    omega
  · change 60 ≤ (17 : ℕ) at hlo
    omega
  · change 60 ≤ (18 : ℕ) at hlo
    omega
  · change 60 ≤ (19 : ℕ) at hlo
    omega
  · change 60 ≤ (20 : ℕ) at hlo
    omega
  · change 60 ≤ (21 : ℕ) at hlo
    omega
  · change 60 ≤ (22 : ℕ) at hlo
    omega
  · change 60 ≤ (23 : ℕ) at hlo
    omega
  · change 60 ≤ (24 : ℕ) at hlo
    omega
  · change 60 ≤ (25 : ℕ) at hlo
    omega
  · change 60 ≤ (26 : ℕ) at hlo
    omega
  · change 60 ≤ (27 : ℕ) at hlo
    omega
  · change 60 ≤ (28 : ℕ) at hlo
    omega
  · change 60 ≤ (29 : ℕ) at hlo
    omega
  · change 60 ≤ (30 : ℕ) at hlo
    omega
  · change 60 ≤ (31 : ℕ) at hlo
    omega
  · change 60 ≤ (32 : ℕ) at hlo
    omega
  · change 60 ≤ (33 : ℕ) at hlo
    omega
  · change 60 ≤ (34 : ℕ) at hlo
    omega
  · change 60 ≤ (35 : ℕ) at hlo
    omega
  · change 60 ≤ (36 : ℕ) at hlo
    omega
  · change 60 ≤ (37 : ℕ) at hlo
    omega
  · change 60 ≤ (38 : ℕ) at hlo
    omega
  · change 60 ≤ (39 : ℕ) at hlo
    omega
  · change 60 ≤ (40 : ℕ) at hlo
    omega
  · change 60 ≤ (41 : ℕ) at hlo
    omega
  · change 60 ≤ (42 : ℕ) at hlo
    omega
  · change 60 ≤ (43 : ℕ) at hlo
    omega
  · change 60 ≤ (44 : ℕ) at hlo
    omega
  · change 60 ≤ (45 : ℕ) at hlo
    omega
  · change 60 ≤ (46 : ℕ) at hlo
    omega
  · change 60 ≤ (47 : ℕ) at hlo
    omega
  · change 60 ≤ (48 : ℕ) at hlo
    omega
  · change 60 ≤ (49 : ℕ) at hlo
    omega
  · change 60 ≤ (50 : ℕ) at hlo
    omega
  · change 60 ≤ (51 : ℕ) at hlo
    omega
  · change 60 ≤ (52 : ℕ) at hlo
    omega
  · change 60 ≤ (53 : ℕ) at hlo
    omega
  · change 60 ≤ (54 : ℕ) at hlo
    omega
  · change 60 ≤ (55 : ℕ) at hlo
    omega
  · change 60 ≤ (56 : ℕ) at hlo
    omega
  · change 60 ≤ (57 : ℕ) at hlo
    omega
  · change 60 ≤ (58 : ℕ) at hlo
    omega
  · change 60 ≤ (59 : ℕ) at hlo
    omega
  · exact f416_H_rows_15_half0.1 b
  · exact f416_H_rows_15_half0.2 b
  · exact f416_H_rows_15_half1.1 b
  · exact f416_H_rows_15_half1.2 b

#print axioms f416_H_rows_15
end TorusLean.BosonFiniteCertificate
