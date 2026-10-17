import torus.shared.BosonFiniteCertificateNatFourHS416HRows6Half0
import torus.shared.BosonFiniteCertificateNatFourHS416HRows6Half1
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

theorem f416_H_rows_6 (a b : Fin 64) (hlo : 24 ≤ a.val) (hhi : a.val < 28) :
    natFourHWordFormSparse 16 (f416basis a) (f416basis b) = f416rawHForm a b := by
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
  · exact f416_H_rows_6_half0.1 b
  · exact f416_H_rows_6_half0.2 b
  · exact f416_H_rows_6_half1.1 b
  · exact f416_H_rows_6_half1.2 b
  · change (28 : ℕ) < 28 at hhi
    omega
  · change (29 : ℕ) < 28 at hhi
    omega
  · change (30 : ℕ) < 28 at hhi
    omega
  · change (31 : ℕ) < 28 at hhi
    omega
  · change (32 : ℕ) < 28 at hhi
    omega
  · change (33 : ℕ) < 28 at hhi
    omega
  · change (34 : ℕ) < 28 at hhi
    omega
  · change (35 : ℕ) < 28 at hhi
    omega
  · change (36 : ℕ) < 28 at hhi
    omega
  · change (37 : ℕ) < 28 at hhi
    omega
  · change (38 : ℕ) < 28 at hhi
    omega
  · change (39 : ℕ) < 28 at hhi
    omega
  · change (40 : ℕ) < 28 at hhi
    omega
  · change (41 : ℕ) < 28 at hhi
    omega
  · change (42 : ℕ) < 28 at hhi
    omega
  · change (43 : ℕ) < 28 at hhi
    omega
  · change (44 : ℕ) < 28 at hhi
    omega
  · change (45 : ℕ) < 28 at hhi
    omega
  · change (46 : ℕ) < 28 at hhi
    omega
  · change (47 : ℕ) < 28 at hhi
    omega
  · change (48 : ℕ) < 28 at hhi
    omega
  · change (49 : ℕ) < 28 at hhi
    omega
  · change (50 : ℕ) < 28 at hhi
    omega
  · change (51 : ℕ) < 28 at hhi
    omega
  · change (52 : ℕ) < 28 at hhi
    omega
  · change (53 : ℕ) < 28 at hhi
    omega
  · change (54 : ℕ) < 28 at hhi
    omega
  · change (55 : ℕ) < 28 at hhi
    omega
  · change (56 : ℕ) < 28 at hhi
    omega
  · change (57 : ℕ) < 28 at hhi
    omega
  · change (58 : ℕ) < 28 at hhi
    omega
  · change (59 : ℕ) < 28 at hhi
    omega
  · change (60 : ℕ) < 28 at hhi
    omega
  · change (61 : ℕ) < 28 at hhi
    omega
  · change (62 : ℕ) < 28 at hhi
    omega
  · change (63 : ℕ) < 28 at hhi
    omega

#print axioms f416_H_rows_6
end TorusLean.BosonFiniteCertificate
