import torus.shared.BosonFiniteCertificateNatFourHS416HRows5Half0
import torus.shared.BosonFiniteCertificateNatFourHS416HRows5Half1
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

theorem f416_H_rows_5 (a b : Fin 64) (hlo : 20 ≤ a.val) (hhi : a.val < 24) :
    natFourHWordFormSparse 16 (f416basis a) (f416basis b) = f416rawHForm a b := by
  fin_cases a
  · change 20 ≤ (0 : ℕ) at hlo
    omega
  · change 20 ≤ (1 : ℕ) at hlo
    omega
  · change 20 ≤ (2 : ℕ) at hlo
    omega
  · change 20 ≤ (3 : ℕ) at hlo
    omega
  · change 20 ≤ (4 : ℕ) at hlo
    omega
  · change 20 ≤ (5 : ℕ) at hlo
    omega
  · change 20 ≤ (6 : ℕ) at hlo
    omega
  · change 20 ≤ (7 : ℕ) at hlo
    omega
  · change 20 ≤ (8 : ℕ) at hlo
    omega
  · change 20 ≤ (9 : ℕ) at hlo
    omega
  · change 20 ≤ (10 : ℕ) at hlo
    omega
  · change 20 ≤ (11 : ℕ) at hlo
    omega
  · change 20 ≤ (12 : ℕ) at hlo
    omega
  · change 20 ≤ (13 : ℕ) at hlo
    omega
  · change 20 ≤ (14 : ℕ) at hlo
    omega
  · change 20 ≤ (15 : ℕ) at hlo
    omega
  · change 20 ≤ (16 : ℕ) at hlo
    omega
  · change 20 ≤ (17 : ℕ) at hlo
    omega
  · change 20 ≤ (18 : ℕ) at hlo
    omega
  · change 20 ≤ (19 : ℕ) at hlo
    omega
  · exact f416_H_rows_5_half0.1 b
  · exact f416_H_rows_5_half0.2 b
  · exact f416_H_rows_5_half1.1 b
  · exact f416_H_rows_5_half1.2 b
  · change (24 : ℕ) < 24 at hhi
    omega
  · change (25 : ℕ) < 24 at hhi
    omega
  · change (26 : ℕ) < 24 at hhi
    omega
  · change (27 : ℕ) < 24 at hhi
    omega
  · change (28 : ℕ) < 24 at hhi
    omega
  · change (29 : ℕ) < 24 at hhi
    omega
  · change (30 : ℕ) < 24 at hhi
    omega
  · change (31 : ℕ) < 24 at hhi
    omega
  · change (32 : ℕ) < 24 at hhi
    omega
  · change (33 : ℕ) < 24 at hhi
    omega
  · change (34 : ℕ) < 24 at hhi
    omega
  · change (35 : ℕ) < 24 at hhi
    omega
  · change (36 : ℕ) < 24 at hhi
    omega
  · change (37 : ℕ) < 24 at hhi
    omega
  · change (38 : ℕ) < 24 at hhi
    omega
  · change (39 : ℕ) < 24 at hhi
    omega
  · change (40 : ℕ) < 24 at hhi
    omega
  · change (41 : ℕ) < 24 at hhi
    omega
  · change (42 : ℕ) < 24 at hhi
    omega
  · change (43 : ℕ) < 24 at hhi
    omega
  · change (44 : ℕ) < 24 at hhi
    omega
  · change (45 : ℕ) < 24 at hhi
    omega
  · change (46 : ℕ) < 24 at hhi
    omega
  · change (47 : ℕ) < 24 at hhi
    omega
  · change (48 : ℕ) < 24 at hhi
    omega
  · change (49 : ℕ) < 24 at hhi
    omega
  · change (50 : ℕ) < 24 at hhi
    omega
  · change (51 : ℕ) < 24 at hhi
    omega
  · change (52 : ℕ) < 24 at hhi
    omega
  · change (53 : ℕ) < 24 at hhi
    omega
  · change (54 : ℕ) < 24 at hhi
    omega
  · change (55 : ℕ) < 24 at hhi
    omega
  · change (56 : ℕ) < 24 at hhi
    omega
  · change (57 : ℕ) < 24 at hhi
    omega
  · change (58 : ℕ) < 24 at hhi
    omega
  · change (59 : ℕ) < 24 at hhi
    omega
  · change (60 : ℕ) < 24 at hhi
    omega
  · change (61 : ℕ) < 24 at hhi
    omega
  · change (62 : ℕ) < 24 at hhi
    omega
  · change (63 : ℕ) < 24 at hhi
    omega

#print axioms f416_H_rows_5
end TorusLean.BosonFiniteCertificate
