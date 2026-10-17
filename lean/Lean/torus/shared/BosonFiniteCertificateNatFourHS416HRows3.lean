import torus.shared.BosonFiniteCertificateNatFourHS416HRows3Half0
import torus.shared.BosonFiniteCertificateNatFourHS416HRows3Half1
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

theorem f416_H_rows_3 (a b : Fin 64) (hlo : 12 ≤ a.val) (hhi : a.val < 16) :
    natFourHWordFormSparse 16 (f416basis a) (f416basis b) = f416rawHForm a b := by
  fin_cases a
  · change 12 ≤ (0 : ℕ) at hlo
    omega
  · change 12 ≤ (1 : ℕ) at hlo
    omega
  · change 12 ≤ (2 : ℕ) at hlo
    omega
  · change 12 ≤ (3 : ℕ) at hlo
    omega
  · change 12 ≤ (4 : ℕ) at hlo
    omega
  · change 12 ≤ (5 : ℕ) at hlo
    omega
  · change 12 ≤ (6 : ℕ) at hlo
    omega
  · change 12 ≤ (7 : ℕ) at hlo
    omega
  · change 12 ≤ (8 : ℕ) at hlo
    omega
  · change 12 ≤ (9 : ℕ) at hlo
    omega
  · change 12 ≤ (10 : ℕ) at hlo
    omega
  · change 12 ≤ (11 : ℕ) at hlo
    omega
  · exact f416_H_rows_3_half0.1 b
  · exact f416_H_rows_3_half0.2 b
  · exact f416_H_rows_3_half1.1 b
  · exact f416_H_rows_3_half1.2 b
  · change (16 : ℕ) < 16 at hhi
    omega
  · change (17 : ℕ) < 16 at hhi
    omega
  · change (18 : ℕ) < 16 at hhi
    omega
  · change (19 : ℕ) < 16 at hhi
    omega
  · change (20 : ℕ) < 16 at hhi
    omega
  · change (21 : ℕ) < 16 at hhi
    omega
  · change (22 : ℕ) < 16 at hhi
    omega
  · change (23 : ℕ) < 16 at hhi
    omega
  · change (24 : ℕ) < 16 at hhi
    omega
  · change (25 : ℕ) < 16 at hhi
    omega
  · change (26 : ℕ) < 16 at hhi
    omega
  · change (27 : ℕ) < 16 at hhi
    omega
  · change (28 : ℕ) < 16 at hhi
    omega
  · change (29 : ℕ) < 16 at hhi
    omega
  · change (30 : ℕ) < 16 at hhi
    omega
  · change (31 : ℕ) < 16 at hhi
    omega
  · change (32 : ℕ) < 16 at hhi
    omega
  · change (33 : ℕ) < 16 at hhi
    omega
  · change (34 : ℕ) < 16 at hhi
    omega
  · change (35 : ℕ) < 16 at hhi
    omega
  · change (36 : ℕ) < 16 at hhi
    omega
  · change (37 : ℕ) < 16 at hhi
    omega
  · change (38 : ℕ) < 16 at hhi
    omega
  · change (39 : ℕ) < 16 at hhi
    omega
  · change (40 : ℕ) < 16 at hhi
    omega
  · change (41 : ℕ) < 16 at hhi
    omega
  · change (42 : ℕ) < 16 at hhi
    omega
  · change (43 : ℕ) < 16 at hhi
    omega
  · change (44 : ℕ) < 16 at hhi
    omega
  · change (45 : ℕ) < 16 at hhi
    omega
  · change (46 : ℕ) < 16 at hhi
    omega
  · change (47 : ℕ) < 16 at hhi
    omega
  · change (48 : ℕ) < 16 at hhi
    omega
  · change (49 : ℕ) < 16 at hhi
    omega
  · change (50 : ℕ) < 16 at hhi
    omega
  · change (51 : ℕ) < 16 at hhi
    omega
  · change (52 : ℕ) < 16 at hhi
    omega
  · change (53 : ℕ) < 16 at hhi
    omega
  · change (54 : ℕ) < 16 at hhi
    omega
  · change (55 : ℕ) < 16 at hhi
    omega
  · change (56 : ℕ) < 16 at hhi
    omega
  · change (57 : ℕ) < 16 at hhi
    omega
  · change (58 : ℕ) < 16 at hhi
    omega
  · change (59 : ℕ) < 16 at hhi
    omega
  · change (60 : ℕ) < 16 at hhi
    omega
  · change (61 : ℕ) < 16 at hhi
    omega
  · change (62 : ℕ) < 16 at hhi
    omega
  · change (63 : ℕ) < 16 at hhi
    omega

#print axioms f416_H_rows_3
end TorusLean.BosonFiniteCertificate
