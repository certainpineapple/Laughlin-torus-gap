import torus.shared.BosonFiniteCertificateNatFourHS416HRows9Half0
import torus.shared.BosonFiniteCertificateNatFourHS416HRows9Half1
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

theorem f416_H_rows_9 (a b : Fin 64) (hlo : 36 ≤ a.val) (hhi : a.val < 40) :
    natFourHWordFormSparse 16 (f416basis a) (f416basis b) = f416rawHForm a b := by
  fin_cases a
  · change 36 ≤ (0 : ℕ) at hlo
    omega
  · change 36 ≤ (1 : ℕ) at hlo
    omega
  · change 36 ≤ (2 : ℕ) at hlo
    omega
  · change 36 ≤ (3 : ℕ) at hlo
    omega
  · change 36 ≤ (4 : ℕ) at hlo
    omega
  · change 36 ≤ (5 : ℕ) at hlo
    omega
  · change 36 ≤ (6 : ℕ) at hlo
    omega
  · change 36 ≤ (7 : ℕ) at hlo
    omega
  · change 36 ≤ (8 : ℕ) at hlo
    omega
  · change 36 ≤ (9 : ℕ) at hlo
    omega
  · change 36 ≤ (10 : ℕ) at hlo
    omega
  · change 36 ≤ (11 : ℕ) at hlo
    omega
  · change 36 ≤ (12 : ℕ) at hlo
    omega
  · change 36 ≤ (13 : ℕ) at hlo
    omega
  · change 36 ≤ (14 : ℕ) at hlo
    omega
  · change 36 ≤ (15 : ℕ) at hlo
    omega
  · change 36 ≤ (16 : ℕ) at hlo
    omega
  · change 36 ≤ (17 : ℕ) at hlo
    omega
  · change 36 ≤ (18 : ℕ) at hlo
    omega
  · change 36 ≤ (19 : ℕ) at hlo
    omega
  · change 36 ≤ (20 : ℕ) at hlo
    omega
  · change 36 ≤ (21 : ℕ) at hlo
    omega
  · change 36 ≤ (22 : ℕ) at hlo
    omega
  · change 36 ≤ (23 : ℕ) at hlo
    omega
  · change 36 ≤ (24 : ℕ) at hlo
    omega
  · change 36 ≤ (25 : ℕ) at hlo
    omega
  · change 36 ≤ (26 : ℕ) at hlo
    omega
  · change 36 ≤ (27 : ℕ) at hlo
    omega
  · change 36 ≤ (28 : ℕ) at hlo
    omega
  · change 36 ≤ (29 : ℕ) at hlo
    omega
  · change 36 ≤ (30 : ℕ) at hlo
    omega
  · change 36 ≤ (31 : ℕ) at hlo
    omega
  · change 36 ≤ (32 : ℕ) at hlo
    omega
  · change 36 ≤ (33 : ℕ) at hlo
    omega
  · change 36 ≤ (34 : ℕ) at hlo
    omega
  · change 36 ≤ (35 : ℕ) at hlo
    omega
  · exact f416_H_rows_9_half0.1 b
  · exact f416_H_rows_9_half0.2 b
  · exact f416_H_rows_9_half1.1 b
  · exact f416_H_rows_9_half1.2 b
  · change (40 : ℕ) < 40 at hhi
    omega
  · change (41 : ℕ) < 40 at hhi
    omega
  · change (42 : ℕ) < 40 at hhi
    omega
  · change (43 : ℕ) < 40 at hhi
    omega
  · change (44 : ℕ) < 40 at hhi
    omega
  · change (45 : ℕ) < 40 at hhi
    omega
  · change (46 : ℕ) < 40 at hhi
    omega
  · change (47 : ℕ) < 40 at hhi
    omega
  · change (48 : ℕ) < 40 at hhi
    omega
  · change (49 : ℕ) < 40 at hhi
    omega
  · change (50 : ℕ) < 40 at hhi
    omega
  · change (51 : ℕ) < 40 at hhi
    omega
  · change (52 : ℕ) < 40 at hhi
    omega
  · change (53 : ℕ) < 40 at hhi
    omega
  · change (54 : ℕ) < 40 at hhi
    omega
  · change (55 : ℕ) < 40 at hhi
    omega
  · change (56 : ℕ) < 40 at hhi
    omega
  · change (57 : ℕ) < 40 at hhi
    omega
  · change (58 : ℕ) < 40 at hhi
    omega
  · change (59 : ℕ) < 40 at hhi
    omega
  · change (60 : ℕ) < 40 at hhi
    omega
  · change (61 : ℕ) < 40 at hhi
    omega
  · change (62 : ℕ) < 40 at hhi
    omega
  · change (63 : ℕ) < 40 at hhi
    omega

#print axioms f416_H_rows_9
end TorusLean.BosonFiniteCertificate
