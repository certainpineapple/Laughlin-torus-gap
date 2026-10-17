import torus.shared.BosonFiniteCertificateNatFourHS416HRows7Half0
import torus.shared.BosonFiniteCertificateNatFourHS416HRows7Half1
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

theorem f416_H_rows_7 (a b : Fin 64) (hlo : 28 ≤ a.val) (hhi : a.val < 32) :
    natFourHWordFormSparse 16 (f416basis a) (f416basis b) = f416rawHForm a b := by
  fin_cases a
  · change 28 ≤ (0 : ℕ) at hlo
    omega
  · change 28 ≤ (1 : ℕ) at hlo
    omega
  · change 28 ≤ (2 : ℕ) at hlo
    omega
  · change 28 ≤ (3 : ℕ) at hlo
    omega
  · change 28 ≤ (4 : ℕ) at hlo
    omega
  · change 28 ≤ (5 : ℕ) at hlo
    omega
  · change 28 ≤ (6 : ℕ) at hlo
    omega
  · change 28 ≤ (7 : ℕ) at hlo
    omega
  · change 28 ≤ (8 : ℕ) at hlo
    omega
  · change 28 ≤ (9 : ℕ) at hlo
    omega
  · change 28 ≤ (10 : ℕ) at hlo
    omega
  · change 28 ≤ (11 : ℕ) at hlo
    omega
  · change 28 ≤ (12 : ℕ) at hlo
    omega
  · change 28 ≤ (13 : ℕ) at hlo
    omega
  · change 28 ≤ (14 : ℕ) at hlo
    omega
  · change 28 ≤ (15 : ℕ) at hlo
    omega
  · change 28 ≤ (16 : ℕ) at hlo
    omega
  · change 28 ≤ (17 : ℕ) at hlo
    omega
  · change 28 ≤ (18 : ℕ) at hlo
    omega
  · change 28 ≤ (19 : ℕ) at hlo
    omega
  · change 28 ≤ (20 : ℕ) at hlo
    omega
  · change 28 ≤ (21 : ℕ) at hlo
    omega
  · change 28 ≤ (22 : ℕ) at hlo
    omega
  · change 28 ≤ (23 : ℕ) at hlo
    omega
  · change 28 ≤ (24 : ℕ) at hlo
    omega
  · change 28 ≤ (25 : ℕ) at hlo
    omega
  · change 28 ≤ (26 : ℕ) at hlo
    omega
  · change 28 ≤ (27 : ℕ) at hlo
    omega
  · exact f416_H_rows_7_half0.1 b
  · exact f416_H_rows_7_half0.2 b
  · exact f416_H_rows_7_half1.1 b
  · exact f416_H_rows_7_half1.2 b
  · change (32 : ℕ) < 32 at hhi
    omega
  · change (33 : ℕ) < 32 at hhi
    omega
  · change (34 : ℕ) < 32 at hhi
    omega
  · change (35 : ℕ) < 32 at hhi
    omega
  · change (36 : ℕ) < 32 at hhi
    omega
  · change (37 : ℕ) < 32 at hhi
    omega
  · change (38 : ℕ) < 32 at hhi
    omega
  · change (39 : ℕ) < 32 at hhi
    omega
  · change (40 : ℕ) < 32 at hhi
    omega
  · change (41 : ℕ) < 32 at hhi
    omega
  · change (42 : ℕ) < 32 at hhi
    omega
  · change (43 : ℕ) < 32 at hhi
    omega
  · change (44 : ℕ) < 32 at hhi
    omega
  · change (45 : ℕ) < 32 at hhi
    omega
  · change (46 : ℕ) < 32 at hhi
    omega
  · change (47 : ℕ) < 32 at hhi
    omega
  · change (48 : ℕ) < 32 at hhi
    omega
  · change (49 : ℕ) < 32 at hhi
    omega
  · change (50 : ℕ) < 32 at hhi
    omega
  · change (51 : ℕ) < 32 at hhi
    omega
  · change (52 : ℕ) < 32 at hhi
    omega
  · change (53 : ℕ) < 32 at hhi
    omega
  · change (54 : ℕ) < 32 at hhi
    omega
  · change (55 : ℕ) < 32 at hhi
    omega
  · change (56 : ℕ) < 32 at hhi
    omega
  · change (57 : ℕ) < 32 at hhi
    omega
  · change (58 : ℕ) < 32 at hhi
    omega
  · change (59 : ℕ) < 32 at hhi
    omega
  · change (60 : ℕ) < 32 at hhi
    omega
  · change (61 : ℕ) < 32 at hhi
    omega
  · change (62 : ℕ) < 32 at hhi
    omega
  · change (63 : ℕ) < 32 at hhi
    omega

#print axioms f416_H_rows_7
end TorusLean.BosonFiniteCertificate
