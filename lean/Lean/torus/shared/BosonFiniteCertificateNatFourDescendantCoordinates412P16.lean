import torus.shared.BosonFiniteCertificateNatFourRaiseSparse415
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates412P15

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

def f412desc4 : Matrix (Fin 64) (Fin 7) ℚ :=
  !![(1/462), (-1/462), (1/330), (-1/462), (1/330), (1/330), (-1/165);
    0, 0, 0, 0, 0, 0, 0;
    (6/77), (-1/154), (-2/385), (1/693), (-67/2310), (-128/3465), (9/110);
    (-8/231), (-17/462), (76/1155), (-1/198), (31/2310), (-2/495), (13/1155);
    (-17/231), (2/77), (46/1155), (17/231), (46/1155), (19/385), (-158/1155);
    (20/77), (2/77), (-36/385), (40/693), (-53/1155), (4/495), (-16/385);
    (-4/21), (-5/42), (-4/105), (-1/9), (-13/210), (-4/315), (19/210);
    (-4/21), (-1/42), (8/105), (-1/42), (1/210), (2/105), (1/21);
    (3/14), (1/14), (3/70), (1/14), (1/70), (1/70), 0;
    (-10/77), (9/154), (-26/385), (5/99), (-101/2310), (-124/3465), (7/110);
    (4/11), (-1/154), (-24/385), (-17/198), (109/2310), (58/693), (-62/385);
    (-268/231), (-1/154), (-4/165), (-317/1386), (461/2310), (818/3465), (-101/231);
    (24/77), (82/231), (-4/11), (4/693), (-167/1155), (-776/3465), (192/385);
    (12/7), (1/21), (4/35), (-2/9), (4/105), (-92/315), (3/5);
    (-68/21), (-1/6), (8/21), (-31/126), (13/30), (22/315), (-10/21);
    (12/7), (3/14), (-24/35), (3/14), (-3/70), (-6/35), (-3/7);
    (87/77), (-9/154), (26/385), (-13/693), (277/2310), (115/693), (-291/770);
    (-128/77), (1/11), (72/385), (437/693), (-433/1155), (-1684/3465), (68/77);
    (24/7), (-6/7), (2/7), (4/63), (-2/15), (-14/45), (33/35);
    (-4/7), (-11/14), (-8/35), (79/126), (13/30), (254/315), (-46/35);
    (-30/7), 0, (6/7), (4/7), (-12/35), (8/35), (-9/35);
    (24/7), (-2/7), (48/35), (-4/7), (-2/5), (-8/35), (24/35);
    (-8/3), (4/21), (52/105), (-17/63), (-2/21), (-8/45), (34/105);
    (80/21), (10/21), (-76/105), (-20/9), (3/5), (80/63), (-262/105);
    (-36/7), (31/14), (-144/35), (11/6), (-67/70), (-26/105), (3/7);
    (16/7), (16/21), (-8/7), (-4/3), (4/5), (-8/105), (10/7);
    (15/7), (-10/21), (6/5), (5/21), (-6/35), (-3/7), (9/35);
    (-24/7), (-59/21), (144/35), (7/3), (1/5), (-52/35), (72/35);
    2, (-1), (4/5), (-4/3), (7/5), (14/15), (-8/5);
    0, 2, (-12/5), (-1/3), (-6/5), (8/15), (-6/5);
    (-20/77), (-2/77), (36/385), (5/231), (2/55), (4/231), (-17/385);
    (6/11), (-31/77), (206/385), (-53/198), (299/1155), (578/3465), (-219/770);
    (-216/77), (32/231), (-8/11), (74/693), (-664/1155), (-184/495), (318/385);
    (22/7), (-1/14), (2/7), (-1/21), (-27/70), (-4/105), (1/14);
    (-4/7), (2/3), (12/7), (13/63), (46/105), (44/63), (-7/5);
    (-30/7), (4/7), (-6/7), (5/14), (-1/5), (2/7), (33/70);
    (24/7), (-4/7), (-48/35), (-2/7), (-12/35), 0, (36/35);
    (204/77), (7/11), (-288/385), (103/231), (-233/385), (-776/1155), (102/77);
    (-48/7), (11/21), (-8/5), (97/63), (-11/105), (-4/63), (-12/35);
    (100/7), (-25/6), (96/35), (-275/126), (631/210), (166/63), (-206/35);
    (-108/7), (27/7), (-108/35), (18/7), (-12/5), (-20/7), (27/7);
    (48/7), (-20/7), (24/5), (-12/7), (48/35), (-8/35), (-6/7);
    (-80/21), 0, (136/105), (10/63), (248/105), (496/315), (-332/105);
    (60/7), (155/42), (-108/35), (55/42), (-29/10), (-374/105), (303/35);
    (-96/7), (40/7), (-48/5), (80/21), (-216/35), (-80/21), (156/35);
    8, (-4/3), (-8/5), (-4/3), (8/5), (16/5), (-10);
    0, (-5), (48/5), (-15/7), (9/7), (4/5), (48/35);
    0, (-13/3), (24/5), (-7/3), (17/5), (12/5), (-12/5);
    0, 4, (-24/5), 2, (-12/5), (-16/5), (36/5);
    (6/7), (6/7), (-12/35), (-8/21), (-2/35), (2/21), (-3/35);
    (-20/7), (-20/7), (152/35), (-200/63), (244/105), (796/315), (-158/35);
    (45/7), (-5/2), (-108/35), (-25/7), (-123/70), (-89/35), (423/70);
    (-72/7), (18/7), (-72/35), (2/7), (-6/35), (-72/35), (162/35);
    6, (-2), (36/5), 0, (22/5), (14/5), (-27/5);
    0, (15/7), (-36/35), (130/21), (-177/35), (-68/15), (60/7);
    0, (50/21), (-264/35), (-50/21), (46/35), (16/3), (-306/35);
    0, 2, (-24/5), (14/3), (-22/5), (32/15), (6/5);
    0, (-35/3), (84/5), (-40/3), (87/5), (268/15), (-186/5);
    0, 7, (-36/5), 8, (-33/5), (-44/5), (54/5);
    0, (80/21), (-64/35), (40/7), (-48/35), (-32/15), (8/7);
    0, (-20/3), (48/5), (-10), (44/5), (56/15), (-42/5);
    0, 4, (-48/5), 6, (-84/5), (-88/5), (198/5);
    0, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 4, 6, (-12)]

theorem f412desc4_step : f415raise*f412desc3=f412desc4 := by
  refine natFourSparseRowProduct_matrix_check f415raise f412desc3 f412desc4
    f415raiseSparseRows f415_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 0) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 1) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 2) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 3) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 4) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 5) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 6) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 7) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 8) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 9) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 10) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 11) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 12) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 13) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 14) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 15) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 16) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 17) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 18) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 19) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 20) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 21) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 22) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 23) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 24) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 25) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 26) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 27) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 28) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 29) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 30) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 31) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 32) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 33) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 34) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 35) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 36) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 37) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 38) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 39) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 40) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 41) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 42) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 43) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 44) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 45) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 46) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 47) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 48) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 49) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 50) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 51) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 52) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 53) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 53 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 54) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 54 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 55) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 55 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 56) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 56 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 57) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 57 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 58) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 58 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 59) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 59 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 60) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 60 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 61) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 61 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 62) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 62 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 63) f412desc3 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc4 63 b)
      (by decide +kernel) 0 b

theorem f412desc4_actual (x : Fin 7 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
      (natFourWordBlock f412basis (complexify b412relative *ᵥ x))=
      natFourWordBlock f416basis (complexify f412desc4 *ᵥ x) := by
  exact natFour_descendant_step 3
    (fun x => natFourWordBlock f412basis (complexify b412relative *ᵥ x))
    f415basis f416basis f412desc3 f412desc4 f415raise
    f412desc3_actual f415_actual_raise_block f412desc4_step x

#print axioms f412desc4_step
#print axioms f412desc4_actual
end TorusLean.BosonFiniteCertificate
