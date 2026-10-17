import torus.shared.BosonFiniteCertificateNatFourHS416HRows13Half0
import torus.shared.BosonFiniteCertificateNatFourHS416HRows13Half1
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

theorem f416_H_rows_13 (a b : Fin 64) (hlo : 52 ≤ a.val) (hhi : a.val < 56) :
    natFourHWordFormSparse 16 (f416basis a) (f416basis b) = f416rawHForm a b := by
  fin_cases a
  · change 52 ≤ (0 : ℕ) at hlo
    omega
  · change 52 ≤ (1 : ℕ) at hlo
    omega
  · change 52 ≤ (2 : ℕ) at hlo
    omega
  · change 52 ≤ (3 : ℕ) at hlo
    omega
  · change 52 ≤ (4 : ℕ) at hlo
    omega
  · change 52 ≤ (5 : ℕ) at hlo
    omega
  · change 52 ≤ (6 : ℕ) at hlo
    omega
  · change 52 ≤ (7 : ℕ) at hlo
    omega
  · change 52 ≤ (8 : ℕ) at hlo
    omega
  · change 52 ≤ (9 : ℕ) at hlo
    omega
  · change 52 ≤ (10 : ℕ) at hlo
    omega
  · change 52 ≤ (11 : ℕ) at hlo
    omega
  · change 52 ≤ (12 : ℕ) at hlo
    omega
  · change 52 ≤ (13 : ℕ) at hlo
    omega
  · change 52 ≤ (14 : ℕ) at hlo
    omega
  · change 52 ≤ (15 : ℕ) at hlo
    omega
  · change 52 ≤ (16 : ℕ) at hlo
    omega
  · change 52 ≤ (17 : ℕ) at hlo
    omega
  · change 52 ≤ (18 : ℕ) at hlo
    omega
  · change 52 ≤ (19 : ℕ) at hlo
    omega
  · change 52 ≤ (20 : ℕ) at hlo
    omega
  · change 52 ≤ (21 : ℕ) at hlo
    omega
  · change 52 ≤ (22 : ℕ) at hlo
    omega
  · change 52 ≤ (23 : ℕ) at hlo
    omega
  · change 52 ≤ (24 : ℕ) at hlo
    omega
  · change 52 ≤ (25 : ℕ) at hlo
    omega
  · change 52 ≤ (26 : ℕ) at hlo
    omega
  · change 52 ≤ (27 : ℕ) at hlo
    omega
  · change 52 ≤ (28 : ℕ) at hlo
    omega
  · change 52 ≤ (29 : ℕ) at hlo
    omega
  · change 52 ≤ (30 : ℕ) at hlo
    omega
  · change 52 ≤ (31 : ℕ) at hlo
    omega
  · change 52 ≤ (32 : ℕ) at hlo
    omega
  · change 52 ≤ (33 : ℕ) at hlo
    omega
  · change 52 ≤ (34 : ℕ) at hlo
    omega
  · change 52 ≤ (35 : ℕ) at hlo
    omega
  · change 52 ≤ (36 : ℕ) at hlo
    omega
  · change 52 ≤ (37 : ℕ) at hlo
    omega
  · change 52 ≤ (38 : ℕ) at hlo
    omega
  · change 52 ≤ (39 : ℕ) at hlo
    omega
  · change 52 ≤ (40 : ℕ) at hlo
    omega
  · change 52 ≤ (41 : ℕ) at hlo
    omega
  · change 52 ≤ (42 : ℕ) at hlo
    omega
  · change 52 ≤ (43 : ℕ) at hlo
    omega
  · change 52 ≤ (44 : ℕ) at hlo
    omega
  · change 52 ≤ (45 : ℕ) at hlo
    omega
  · change 52 ≤ (46 : ℕ) at hlo
    omega
  · change 52 ≤ (47 : ℕ) at hlo
    omega
  · change 52 ≤ (48 : ℕ) at hlo
    omega
  · change 52 ≤ (49 : ℕ) at hlo
    omega
  · change 52 ≤ (50 : ℕ) at hlo
    omega
  · change 52 ≤ (51 : ℕ) at hlo
    omega
  · exact f416_H_rows_13_half0.1 b
  · exact f416_H_rows_13_half0.2 b
  · exact f416_H_rows_13_half1.1 b
  · exact f416_H_rows_13_half1.2 b
  · change (56 : ℕ) < 56 at hhi
    omega
  · change (57 : ℕ) < 56 at hhi
    omega
  · change (58 : ℕ) < 56 at hhi
    omega
  · change (59 : ℕ) < 56 at hhi
    omega
  · change (60 : ℕ) < 56 at hhi
    omega
  · change (61 : ℕ) < 56 at hhi
    omega
  · change (62 : ℕ) < 56 at hhi
    omega
  · change (63 : ℕ) < 56 at hhi
    omega

#print axioms f416_H_rows_13
end TorusLean.BosonFiniteCertificate
