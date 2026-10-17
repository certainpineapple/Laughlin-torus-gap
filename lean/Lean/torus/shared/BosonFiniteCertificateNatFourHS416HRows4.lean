import torus.shared.BosonFiniteCertificateNatFourHS416HRows4Half0
import torus.shared.BosonFiniteCertificateNatFourHS416HRows4Half1
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

theorem f416_H_rows_4 (a b : Fin 64) (hlo : 16 ≤ a.val) (hhi : a.val < 20) :
    natFourHWordFormSparse 16 (f416basis a) (f416basis b) = f416rawHForm a b := by
  fin_cases a
  · change 16 ≤ (0 : ℕ) at hlo
    omega
  · change 16 ≤ (1 : ℕ) at hlo
    omega
  · change 16 ≤ (2 : ℕ) at hlo
    omega
  · change 16 ≤ (3 : ℕ) at hlo
    omega
  · change 16 ≤ (4 : ℕ) at hlo
    omega
  · change 16 ≤ (5 : ℕ) at hlo
    omega
  · change 16 ≤ (6 : ℕ) at hlo
    omega
  · change 16 ≤ (7 : ℕ) at hlo
    omega
  · change 16 ≤ (8 : ℕ) at hlo
    omega
  · change 16 ≤ (9 : ℕ) at hlo
    omega
  · change 16 ≤ (10 : ℕ) at hlo
    omega
  · change 16 ≤ (11 : ℕ) at hlo
    omega
  · change 16 ≤ (12 : ℕ) at hlo
    omega
  · change 16 ≤ (13 : ℕ) at hlo
    omega
  · change 16 ≤ (14 : ℕ) at hlo
    omega
  · change 16 ≤ (15 : ℕ) at hlo
    omega
  · exact f416_H_rows_4_half0.1 b
  · exact f416_H_rows_4_half0.2 b
  · exact f416_H_rows_4_half1.1 b
  · exact f416_H_rows_4_half1.2 b
  · change (20 : ℕ) < 20 at hhi
    omega
  · change (21 : ℕ) < 20 at hhi
    omega
  · change (22 : ℕ) < 20 at hhi
    omega
  · change (23 : ℕ) < 20 at hhi
    omega
  · change (24 : ℕ) < 20 at hhi
    omega
  · change (25 : ℕ) < 20 at hhi
    omega
  · change (26 : ℕ) < 20 at hhi
    omega
  · change (27 : ℕ) < 20 at hhi
    omega
  · change (28 : ℕ) < 20 at hhi
    omega
  · change (29 : ℕ) < 20 at hhi
    omega
  · change (30 : ℕ) < 20 at hhi
    omega
  · change (31 : ℕ) < 20 at hhi
    omega
  · change (32 : ℕ) < 20 at hhi
    omega
  · change (33 : ℕ) < 20 at hhi
    omega
  · change (34 : ℕ) < 20 at hhi
    omega
  · change (35 : ℕ) < 20 at hhi
    omega
  · change (36 : ℕ) < 20 at hhi
    omega
  · change (37 : ℕ) < 20 at hhi
    omega
  · change (38 : ℕ) < 20 at hhi
    omega
  · change (39 : ℕ) < 20 at hhi
    omega
  · change (40 : ℕ) < 20 at hhi
    omega
  · change (41 : ℕ) < 20 at hhi
    omega
  · change (42 : ℕ) < 20 at hhi
    omega
  · change (43 : ℕ) < 20 at hhi
    omega
  · change (44 : ℕ) < 20 at hhi
    omega
  · change (45 : ℕ) < 20 at hhi
    omega
  · change (46 : ℕ) < 20 at hhi
    omega
  · change (47 : ℕ) < 20 at hhi
    omega
  · change (48 : ℕ) < 20 at hhi
    omega
  · change (49 : ℕ) < 20 at hhi
    omega
  · change (50 : ℕ) < 20 at hhi
    omega
  · change (51 : ℕ) < 20 at hhi
    omega
  · change (52 : ℕ) < 20 at hhi
    omega
  · change (53 : ℕ) < 20 at hhi
    omega
  · change (54 : ℕ) < 20 at hhi
    omega
  · change (55 : ℕ) < 20 at hhi
    omega
  · change (56 : ℕ) < 20 at hhi
    omega
  · change (57 : ℕ) < 20 at hhi
    omega
  · change (58 : ℕ) < 20 at hhi
    omega
  · change (59 : ℕ) < 20 at hhi
    omega
  · change (60 : ℕ) < 20 at hhi
    omega
  · change (61 : ℕ) < 20 at hhi
    omega
  · change (62 : ℕ) < 20 at hhi
    omega
  · change (63 : ℕ) < 20 at hhi
    omega

#print axioms f416_H_rows_4
end TorusLean.BosonFiniteCertificate
