import torus.shared.BosonFiniteCertificateNatFourHS416HRows10Half0
import torus.shared.BosonFiniteCertificateNatFourHS416HRows10Half1
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

theorem f416_H_rows_10 (a b : Fin 64) (hlo : 40 ≤ a.val) (hhi : a.val < 44) :
    natFourHWordFormSparse 16 (f416basis a) (f416basis b) = f416rawHForm a b := by
  fin_cases a
  · change 40 ≤ (0 : ℕ) at hlo
    omega
  · change 40 ≤ (1 : ℕ) at hlo
    omega
  · change 40 ≤ (2 : ℕ) at hlo
    omega
  · change 40 ≤ (3 : ℕ) at hlo
    omega
  · change 40 ≤ (4 : ℕ) at hlo
    omega
  · change 40 ≤ (5 : ℕ) at hlo
    omega
  · change 40 ≤ (6 : ℕ) at hlo
    omega
  · change 40 ≤ (7 : ℕ) at hlo
    omega
  · change 40 ≤ (8 : ℕ) at hlo
    omega
  · change 40 ≤ (9 : ℕ) at hlo
    omega
  · change 40 ≤ (10 : ℕ) at hlo
    omega
  · change 40 ≤ (11 : ℕ) at hlo
    omega
  · change 40 ≤ (12 : ℕ) at hlo
    omega
  · change 40 ≤ (13 : ℕ) at hlo
    omega
  · change 40 ≤ (14 : ℕ) at hlo
    omega
  · change 40 ≤ (15 : ℕ) at hlo
    omega
  · change 40 ≤ (16 : ℕ) at hlo
    omega
  · change 40 ≤ (17 : ℕ) at hlo
    omega
  · change 40 ≤ (18 : ℕ) at hlo
    omega
  · change 40 ≤ (19 : ℕ) at hlo
    omega
  · change 40 ≤ (20 : ℕ) at hlo
    omega
  · change 40 ≤ (21 : ℕ) at hlo
    omega
  · change 40 ≤ (22 : ℕ) at hlo
    omega
  · change 40 ≤ (23 : ℕ) at hlo
    omega
  · change 40 ≤ (24 : ℕ) at hlo
    omega
  · change 40 ≤ (25 : ℕ) at hlo
    omega
  · change 40 ≤ (26 : ℕ) at hlo
    omega
  · change 40 ≤ (27 : ℕ) at hlo
    omega
  · change 40 ≤ (28 : ℕ) at hlo
    omega
  · change 40 ≤ (29 : ℕ) at hlo
    omega
  · change 40 ≤ (30 : ℕ) at hlo
    omega
  · change 40 ≤ (31 : ℕ) at hlo
    omega
  · change 40 ≤ (32 : ℕ) at hlo
    omega
  · change 40 ≤ (33 : ℕ) at hlo
    omega
  · change 40 ≤ (34 : ℕ) at hlo
    omega
  · change 40 ≤ (35 : ℕ) at hlo
    omega
  · change 40 ≤ (36 : ℕ) at hlo
    omega
  · change 40 ≤ (37 : ℕ) at hlo
    omega
  · change 40 ≤ (38 : ℕ) at hlo
    omega
  · change 40 ≤ (39 : ℕ) at hlo
    omega
  · exact f416_H_rows_10_half0.1 b
  · exact f416_H_rows_10_half0.2 b
  · exact f416_H_rows_10_half1.1 b
  · exact f416_H_rows_10_half1.2 b
  · change (44 : ℕ) < 44 at hhi
    omega
  · change (45 : ℕ) < 44 at hhi
    omega
  · change (46 : ℕ) < 44 at hhi
    omega
  · change (47 : ℕ) < 44 at hhi
    omega
  · change (48 : ℕ) < 44 at hhi
    omega
  · change (49 : ℕ) < 44 at hhi
    omega
  · change (50 : ℕ) < 44 at hhi
    omega
  · change (51 : ℕ) < 44 at hhi
    omega
  · change (52 : ℕ) < 44 at hhi
    omega
  · change (53 : ℕ) < 44 at hhi
    omega
  · change (54 : ℕ) < 44 at hhi
    omega
  · change (55 : ℕ) < 44 at hhi
    omega
  · change (56 : ℕ) < 44 at hhi
    omega
  · change (57 : ℕ) < 44 at hhi
    omega
  · change (58 : ℕ) < 44 at hhi
    omega
  · change (59 : ℕ) < 44 at hhi
    omega
  · change (60 : ℕ) < 44 at hhi
    omega
  · change (61 : ℕ) < 44 at hhi
    omega
  · change (62 : ℕ) < 44 at hhi
    omega
  · change (63 : ℕ) < 44 at hhi
    omega

#print axioms f416_H_rows_10
end TorusLean.BosonFiniteCertificate
