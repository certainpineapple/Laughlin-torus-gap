import torus.shared.BosonFiniteCertificateNatFourHS416HRows14Half0
import torus.shared.BosonFiniteCertificateNatFourHS416HRows14Half1
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate

theorem f416_H_rows_14 (a b : Fin 64) (hlo : 56 ≤ a.val) (hhi : a.val < 60) :
    natFourHWordFormSparse 16 (f416basis a) (f416basis b) = f416rawHForm a b := by
  fin_cases a
  · change 56 ≤ (0 : ℕ) at hlo
    omega
  · change 56 ≤ (1 : ℕ) at hlo
    omega
  · change 56 ≤ (2 : ℕ) at hlo
    omega
  · change 56 ≤ (3 : ℕ) at hlo
    omega
  · change 56 ≤ (4 : ℕ) at hlo
    omega
  · change 56 ≤ (5 : ℕ) at hlo
    omega
  · change 56 ≤ (6 : ℕ) at hlo
    omega
  · change 56 ≤ (7 : ℕ) at hlo
    omega
  · change 56 ≤ (8 : ℕ) at hlo
    omega
  · change 56 ≤ (9 : ℕ) at hlo
    omega
  · change 56 ≤ (10 : ℕ) at hlo
    omega
  · change 56 ≤ (11 : ℕ) at hlo
    omega
  · change 56 ≤ (12 : ℕ) at hlo
    omega
  · change 56 ≤ (13 : ℕ) at hlo
    omega
  · change 56 ≤ (14 : ℕ) at hlo
    omega
  · change 56 ≤ (15 : ℕ) at hlo
    omega
  · change 56 ≤ (16 : ℕ) at hlo
    omega
  · change 56 ≤ (17 : ℕ) at hlo
    omega
  · change 56 ≤ (18 : ℕ) at hlo
    omega
  · change 56 ≤ (19 : ℕ) at hlo
    omega
  · change 56 ≤ (20 : ℕ) at hlo
    omega
  · change 56 ≤ (21 : ℕ) at hlo
    omega
  · change 56 ≤ (22 : ℕ) at hlo
    omega
  · change 56 ≤ (23 : ℕ) at hlo
    omega
  · change 56 ≤ (24 : ℕ) at hlo
    omega
  · change 56 ≤ (25 : ℕ) at hlo
    omega
  · change 56 ≤ (26 : ℕ) at hlo
    omega
  · change 56 ≤ (27 : ℕ) at hlo
    omega
  · change 56 ≤ (28 : ℕ) at hlo
    omega
  · change 56 ≤ (29 : ℕ) at hlo
    omega
  · change 56 ≤ (30 : ℕ) at hlo
    omega
  · change 56 ≤ (31 : ℕ) at hlo
    omega
  · change 56 ≤ (32 : ℕ) at hlo
    omega
  · change 56 ≤ (33 : ℕ) at hlo
    omega
  · change 56 ≤ (34 : ℕ) at hlo
    omega
  · change 56 ≤ (35 : ℕ) at hlo
    omega
  · change 56 ≤ (36 : ℕ) at hlo
    omega
  · change 56 ≤ (37 : ℕ) at hlo
    omega
  · change 56 ≤ (38 : ℕ) at hlo
    omega
  · change 56 ≤ (39 : ℕ) at hlo
    omega
  · change 56 ≤ (40 : ℕ) at hlo
    omega
  · change 56 ≤ (41 : ℕ) at hlo
    omega
  · change 56 ≤ (42 : ℕ) at hlo
    omega
  · change 56 ≤ (43 : ℕ) at hlo
    omega
  · change 56 ≤ (44 : ℕ) at hlo
    omega
  · change 56 ≤ (45 : ℕ) at hlo
    omega
  · change 56 ≤ (46 : ℕ) at hlo
    omega
  · change 56 ≤ (47 : ℕ) at hlo
    omega
  · change 56 ≤ (48 : ℕ) at hlo
    omega
  · change 56 ≤ (49 : ℕ) at hlo
    omega
  · change 56 ≤ (50 : ℕ) at hlo
    omega
  · change 56 ≤ (51 : ℕ) at hlo
    omega
  · change 56 ≤ (52 : ℕ) at hlo
    omega
  · change 56 ≤ (53 : ℕ) at hlo
    omega
  · change 56 ≤ (54 : ℕ) at hlo
    omega
  · change 56 ≤ (55 : ℕ) at hlo
    omega
  · exact f416_H_rows_14_half0.1 b
  · exact f416_H_rows_14_half0.2 b
  · exact f416_H_rows_14_half1.1 b
  · exact f416_H_rows_14_half1.2 b
  · change (60 : ℕ) < 60 at hhi
    omega
  · change (61 : ℕ) < 60 at hhi
    omega
  · change (62 : ℕ) < 60 at hhi
    omega
  · change (63 : ℕ) < 60 at hhi
    omega

#print axioms f416_H_rows_14
end TorusLean.BosonFiniteCertificate
