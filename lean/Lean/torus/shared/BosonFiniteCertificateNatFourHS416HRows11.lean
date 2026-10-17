import torus.shared.BosonFiniteCertificateNatFourHS416HRows11Half0
import torus.shared.BosonFiniteCertificateNatFourHS416HRows11Half1
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

theorem f416_H_rows_11 (a b : Fin 64) (hlo : 44 ≤ a.val) (hhi : a.val < 48) :
    natFourHWordFormSparse 16 (f416basis a) (f416basis b) = f416rawHForm a b := by
  fin_cases a
  · change 44 ≤ (0 : ℕ) at hlo
    omega
  · change 44 ≤ (1 : ℕ) at hlo
    omega
  · change 44 ≤ (2 : ℕ) at hlo
    omega
  · change 44 ≤ (3 : ℕ) at hlo
    omega
  · change 44 ≤ (4 : ℕ) at hlo
    omega
  · change 44 ≤ (5 : ℕ) at hlo
    omega
  · change 44 ≤ (6 : ℕ) at hlo
    omega
  · change 44 ≤ (7 : ℕ) at hlo
    omega
  · change 44 ≤ (8 : ℕ) at hlo
    omega
  · change 44 ≤ (9 : ℕ) at hlo
    omega
  · change 44 ≤ (10 : ℕ) at hlo
    omega
  · change 44 ≤ (11 : ℕ) at hlo
    omega
  · change 44 ≤ (12 : ℕ) at hlo
    omega
  · change 44 ≤ (13 : ℕ) at hlo
    omega
  · change 44 ≤ (14 : ℕ) at hlo
    omega
  · change 44 ≤ (15 : ℕ) at hlo
    omega
  · change 44 ≤ (16 : ℕ) at hlo
    omega
  · change 44 ≤ (17 : ℕ) at hlo
    omega
  · change 44 ≤ (18 : ℕ) at hlo
    omega
  · change 44 ≤ (19 : ℕ) at hlo
    omega
  · change 44 ≤ (20 : ℕ) at hlo
    omega
  · change 44 ≤ (21 : ℕ) at hlo
    omega
  · change 44 ≤ (22 : ℕ) at hlo
    omega
  · change 44 ≤ (23 : ℕ) at hlo
    omega
  · change 44 ≤ (24 : ℕ) at hlo
    omega
  · change 44 ≤ (25 : ℕ) at hlo
    omega
  · change 44 ≤ (26 : ℕ) at hlo
    omega
  · change 44 ≤ (27 : ℕ) at hlo
    omega
  · change 44 ≤ (28 : ℕ) at hlo
    omega
  · change 44 ≤ (29 : ℕ) at hlo
    omega
  · change 44 ≤ (30 : ℕ) at hlo
    omega
  · change 44 ≤ (31 : ℕ) at hlo
    omega
  · change 44 ≤ (32 : ℕ) at hlo
    omega
  · change 44 ≤ (33 : ℕ) at hlo
    omega
  · change 44 ≤ (34 : ℕ) at hlo
    omega
  · change 44 ≤ (35 : ℕ) at hlo
    omega
  · change 44 ≤ (36 : ℕ) at hlo
    omega
  · change 44 ≤ (37 : ℕ) at hlo
    omega
  · change 44 ≤ (38 : ℕ) at hlo
    omega
  · change 44 ≤ (39 : ℕ) at hlo
    omega
  · change 44 ≤ (40 : ℕ) at hlo
    omega
  · change 44 ≤ (41 : ℕ) at hlo
    omega
  · change 44 ≤ (42 : ℕ) at hlo
    omega
  · change 44 ≤ (43 : ℕ) at hlo
    omega
  · exact f416_H_rows_11_half0.1 b
  · exact f416_H_rows_11_half0.2 b
  · exact f416_H_rows_11_half1.1 b
  · exact f416_H_rows_11_half1.2 b
  · change (48 : ℕ) < 48 at hhi
    omega
  · change (49 : ℕ) < 48 at hhi
    omega
  · change (50 : ℕ) < 48 at hhi
    omega
  · change (51 : ℕ) < 48 at hhi
    omega
  · change (52 : ℕ) < 48 at hhi
    omega
  · change (53 : ℕ) < 48 at hhi
    omega
  · change (54 : ℕ) < 48 at hhi
    omega
  · change (55 : ℕ) < 48 at hhi
    omega
  · change (56 : ℕ) < 48 at hhi
    omega
  · change (57 : ℕ) < 48 at hhi
    omega
  · change (58 : ℕ) < 48 at hhi
    omega
  · change (59 : ℕ) < 48 at hhi
    omega
  · change (60 : ℕ) < 48 at hhi
    omega
  · change (61 : ℕ) < 48 at hhi
    omega
  · change (62 : ℕ) < 48 at hhi
    omega
  · change (63 : ℕ) < 48 at hhi
    omega

#print axioms f416_H_rows_11
end TorusLean.BosonFiniteCertificate
