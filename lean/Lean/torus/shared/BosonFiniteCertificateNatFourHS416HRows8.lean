import torus.shared.BosonFiniteCertificateNatFourHS416HRows8Half0
import torus.shared.BosonFiniteCertificateNatFourHS416HRows8Half1
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

theorem f416_H_rows_8 (a b : Fin 64) (hlo : 32 ≤ a.val) (hhi : a.val < 36) :
    natFourHWordFormSparse 16 (f416basis a) (f416basis b) = f416rawHForm a b := by
  fin_cases a
  · change 32 ≤ (0 : ℕ) at hlo
    omega
  · change 32 ≤ (1 : ℕ) at hlo
    omega
  · change 32 ≤ (2 : ℕ) at hlo
    omega
  · change 32 ≤ (3 : ℕ) at hlo
    omega
  · change 32 ≤ (4 : ℕ) at hlo
    omega
  · change 32 ≤ (5 : ℕ) at hlo
    omega
  · change 32 ≤ (6 : ℕ) at hlo
    omega
  · change 32 ≤ (7 : ℕ) at hlo
    omega
  · change 32 ≤ (8 : ℕ) at hlo
    omega
  · change 32 ≤ (9 : ℕ) at hlo
    omega
  · change 32 ≤ (10 : ℕ) at hlo
    omega
  · change 32 ≤ (11 : ℕ) at hlo
    omega
  · change 32 ≤ (12 : ℕ) at hlo
    omega
  · change 32 ≤ (13 : ℕ) at hlo
    omega
  · change 32 ≤ (14 : ℕ) at hlo
    omega
  · change 32 ≤ (15 : ℕ) at hlo
    omega
  · change 32 ≤ (16 : ℕ) at hlo
    omega
  · change 32 ≤ (17 : ℕ) at hlo
    omega
  · change 32 ≤ (18 : ℕ) at hlo
    omega
  · change 32 ≤ (19 : ℕ) at hlo
    omega
  · change 32 ≤ (20 : ℕ) at hlo
    omega
  · change 32 ≤ (21 : ℕ) at hlo
    omega
  · change 32 ≤ (22 : ℕ) at hlo
    omega
  · change 32 ≤ (23 : ℕ) at hlo
    omega
  · change 32 ≤ (24 : ℕ) at hlo
    omega
  · change 32 ≤ (25 : ℕ) at hlo
    omega
  · change 32 ≤ (26 : ℕ) at hlo
    omega
  · change 32 ≤ (27 : ℕ) at hlo
    omega
  · change 32 ≤ (28 : ℕ) at hlo
    omega
  · change 32 ≤ (29 : ℕ) at hlo
    omega
  · change 32 ≤ (30 : ℕ) at hlo
    omega
  · change 32 ≤ (31 : ℕ) at hlo
    omega
  · exact f416_H_rows_8_half0.1 b
  · exact f416_H_rows_8_half0.2 b
  · exact f416_H_rows_8_half1.1 b
  · exact f416_H_rows_8_half1.2 b
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
  · change (47 : ℕ) < 36 at hhi
    omega
  · change (48 : ℕ) < 36 at hhi
    omega
  · change (49 : ℕ) < 36 at hhi
    omega
  · change (50 : ℕ) < 36 at hhi
    omega
  · change (51 : ℕ) < 36 at hhi
    omega
  · change (52 : ℕ) < 36 at hhi
    omega
  · change (53 : ℕ) < 36 at hhi
    omega
  · change (54 : ℕ) < 36 at hhi
    omega
  · change (55 : ℕ) < 36 at hhi
    omega
  · change (56 : ℕ) < 36 at hhi
    omega
  · change (57 : ℕ) < 36 at hhi
    omega
  · change (58 : ℕ) < 36 at hhi
    omega
  · change (59 : ℕ) < 36 at hhi
    omega
  · change (60 : ℕ) < 36 at hhi
    omega
  · change (61 : ℕ) < 36 at hhi
    omega
  · change (62 : ℕ) < 36 at hhi
    omega
  · change (63 : ℕ) < 36 at hhi
    omega

#print axioms f416_H_rows_8
end TorusLean.BosonFiniteCertificate
