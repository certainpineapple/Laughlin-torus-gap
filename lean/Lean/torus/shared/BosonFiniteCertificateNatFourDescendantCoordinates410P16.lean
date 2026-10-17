import torus.shared.BosonFiniteCertificateNatFourRaiseSparse415
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates410P15

/-! True all-level COM descendant coordinates, independently of any M4
form matrix. These columns are built from the original relative columns
using already proved actions of the genuine Nat COM raising operator. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

def f410desc6 : Matrix (Fin 64) (Fin 5) ℚ :=
  !![(-1/126), (1/126), (1/126), (-1/84), (-1/84);
    (-4/63), (4/63), (4/63), (-2/21), (-2/21);
    (-5/21), (4/105), (1/105), (1/35), (2/35);
    (-10/21), (8/105), (-2/21), (1/4), (13/35);
    (-5/63), (88/315), (-47/315), (1/15), (41/210);
    (4/21), (22/105), (-38/105), (-1/4), (-3/7);
    (-11/21), (-8/105), (-53/105), 0, (-4/7);
    (-10/63), (10/63), (-4/315), (10/21), (-16/105);
    (5/14), (17/70), (3/14), (9/28), (1/20);
    (5/21), (-4/105), (-1/105), (-1/35), (-2/35);
    0, (-4/5), (-4/7), (27/28), (31/35);
    (-10/63), (-76/315), (86/315), (31/84), (53/105);
    (100/21), (46/105), (166/105), (-257/140), (-57/35);
    (6/7), (-58/35), (12/35), (-27/28), (-5/7);
    (-380/63), (-746/315), (-14/45), (8/21), (202/105);
    (30/7), (18/35), (64/35), (-12/7), (62/35);
    (-10/3), (-2/3), (-2/21), (13/70), (-13/70);
    (-160/21), (44/105), (164/105), (-20/7), (-4);
    (20/7), (8/7), (16/35), (-6/7), (-13/35);
    (-260/21), (208/105), (-4/3), (493/140), (241/35);
    (-50/7), (36/7), (-6/5), (-9/7), (86/35);
    (60/7), (24/7), (-4/7), (-117/35), (-68/35);
    (30/7), (4/35), (-10/7), (-1/7), (-4/5);
    (1100/63), (34/63), (-26/9), (481/84), (145/21);
    (-90/7), (6/7), 4, (39/14), (8/7);
    (40/3), (-104/15), (-32/15), 1, (-52/5);
    (-25/7), (4/7), 7, (-15/7), (-29/14);
    (-20), (-8/5), 12, (-87/10), (-58/5);
    (20/3), (-52/15), (-52/15), (1/5), (-11/5);
    6, (32/5), (-38/5), (-3/2), 6;
    (10/7), (-8/35), (-2/7), (3/14), (6/35);
    (85/21), (16/105), (-53/105), (13/140), (1/5);
    (20/3), (32/15), (52/21), (-17/7), (-76/35);
    (95/7), (-34/35), (15/7), (51/140), (-3/5);
    (-170/21), (-536/105), (-86/105), (53/10), (102/35);
    (-45/7), (-146/35), (-5/7), (9/7), (-48/35);
    (60/7), (-48/35), (4/35), (-9/5), (-108/35);
    (-80/7), (148/35), (76/35), (-132/35), (-102/35);
    (-20/7), (44/35), (-72/35), (6/7), (48/35);
    (200/21), (-74/21), (-230/21), (197/14), 12;
    (-450/7), (486/35), (-12/35), (45/28), (-81/35);
    (240/7), (40/7), (-24/7), (-15/7), (-12);
    (2500/63), (-736/63), (-1060/63), (209/21), (212/21);
    (150/7), (-24/7), (-86/7), (-393/28), (-59/7);
    (-240/7), (-96/7), (-48/35), (36/7), (32/5);
    40, (-152/5), (-16), 33, (144/5);
    (-300/7), (48/7), (100/7), (-351/14), (-18);
    0, (-8/5), (-24/5), (75/2), (238/5);
    12, (48/5), (-12/5), 9, 12;
    (-130/7), (4/7), (10/7), (6/35), (39/35);
    (-100/21), (-320/21), (-44/21), (94/7), (86/7);
    (-150/7), (150/7), (138/7), (-45/2), (-291/14);
    (-240/7), (240/7), (192/7), (-1143/35), (-96/5);
    30, (4/5), (18/5), (-6/5), (39/5);
    (450/7), (-72/7), (46/7), (-15/7), (-8);
    (-400/7), (400/7), (320/7), (-507/7), (-68);
    40, (-304/5), (-152/5), 45, (324/5);
    (-50), 24, 18, (-48), (-68);
    30, 24, (138/5), (-72), (-564/5);
    (400/21), (-64/21), (-208/21), (148/7), 16;
    (-100/3), (-128/3), (-236/3), 119, 116;
    20, (-208/5), (-36), 51, (276/5);
    0, 24, 32, (-36), (-24);
    0, 15, 20, (-45/2), (-15)]

theorem f410desc6_step : f415raise*f410desc5=f410desc6 := by
  refine natFourSparseRowProduct_matrix_check f415raise f410desc5 f410desc6
    f415raiseSparseRows f415_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 0) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 1) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 2) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 3) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 4) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 5) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 6) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 7) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 8) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 9) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 10) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 11) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 12) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 13) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 14) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 15) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 16) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 17) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 18) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 19) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 20) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 21) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 22) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 23) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 24) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 25) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 26) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 27) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 28) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 29) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 30) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 31) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 32) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 33) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 34) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 35) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 36) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 37) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 38) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 39) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 40) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 41) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 42) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 43) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 44) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 45) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 46) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 47) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 48) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 49) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 50) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 51) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 52) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 53) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 53 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 54) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 54 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 55) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 55 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 56) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 56 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 57) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 57 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 58) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 58 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 59) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 59 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 60) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 60 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 61) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 61 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 62) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 62 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f415raiseSparseRows 63) f410desc5 b)
      (fun (_ : Fin 1) (b : Fin 5) => f410desc6 63 b)
      (by decide +kernel) 0 b

theorem f410desc6_actual (x : Fin 5 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6]
      (natFourWordBlock f410basis (complexify b410relative *ᵥ x))=
      natFourWordBlock f416basis (complexify f410desc6 *ᵥ x) := by
  exact natFour_descendant_step 5
    (fun x => natFourWordBlock f410basis (complexify b410relative *ᵥ x))
    f415basis f416basis f410desc5 f410desc6 f415raise
    f410desc5_actual f415_actual_raise_block f410desc6_step x

#print axioms f410desc6_step
#print axioms f410desc6_actual
end TorusLean.BosonFiniteCertificate
