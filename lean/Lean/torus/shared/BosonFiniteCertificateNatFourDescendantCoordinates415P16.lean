import torus.shared.BosonFiniteCertificateNatFourRaiseSparse415
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates415P15

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

def f415desc1 : Matrix (Fin 64) (Fin 7) ℚ :=
  !![(1/3432), (-1/3003), (1/2002), (-1/3003), (1/2002), (1/2002), (-1/1001);
    (-1/286), (4/1001), (-6/1001), (4/1001), (-6/1001), (-6/1001), (12/1001);
    (31/1716), (-12/1001), (95/6006), (-59/6006), (97/9009), (3/364), (-202/15015);
    (-49/858), (53/3003), (-25/1716), (53/3003), (-239/36036), (-8/3003), (-3/715);
    (7/66), (-5/462), (-5/924), (-1/77), (-23/2772), (-4/693), (19/1155);
    (-7/66), (-3/308), (19/924), (-3/308), (5/396), (2/231), (-3/385);
    0, (1/42), (-1/84), (1/42), (-1/252), (-1/252), 0;
    (1/6), (-1/84), 0, (-1/84), 0, 0, 0;
    (-1/8), 0, 0, 0, 0, 0, 0;
    (-1/1716), (-8/1001), (85/6006), (-61/6006), (173/9009), (87/4004), (-698/15015);
    (7/858), (47/1001), (-145/1716), (76/3003), (-2083/36036), (-89/2002), (17/195);
    0, (-1/21), (5/84), (-1/21), (5/252), (-1/63), (3/35);
    0, (-1/308), (85/924), (1/44), (95/924), (53/693), (-73/385);
    0, (3/28), (-17/84), (3/28), (-11/84), (-11/126), (3/35);
    0, (-17/84), (5/42), (-17/84), (5/126), (5/126), 0;
    0, (3/28), 0, (3/28), 0, 0, 0;
    (-7/132), (-9/154), (125/924), (17/462), (89/2772), (-1/132), (1/1155);
    (7/33), (9/154), (-50/231), (-73/462), (8/231), (37/231), (-368/1155);
    (-7/12), (1/14), (-25/84), (4/21), (-79/252), (-3/14), (46/105);
    (7/6), (-3/14), (65/84), (-11/42), (31/84), (1/6), (-19/105);
    (-7/4), (9/14), (-15/28), (2/7), (-3/28), (-1/14), 0;
    1, (-3/7), 0, (-1/7), 0, 0, 0;
    0, (1/6), 0, (1/6), (-1/9), (-11/63), (2/7);
    0, (-65/84), (25/28), (-25/84), (155/252), (20/63), (-53/105);
    0, (9/28), (-25/14), (9/28), (-29/42), (-1/7), (6/35);
    0, (-1/7), (10/7), (-1/7), (4/21), (1/21), 0;
    0, (15/14), (-25/28), 0, (-5/12), (-5/42), (1/7);
    0, (-12/7), (5/2), 0, (31/42), (1/21), (-2/35);
    0, 1, (-5/2), 0, (-1/6), 0, 0;
    0, 0, (1/2), 0, (-1/6), 0, 0;
    (7/858), (-18/1001), (25/858), (1/273), (-1/182), (-137/6006), (122/2145);
    (-7/132), (9/77), (-25/132), (1/42), (-11/252), (9/308), (-17/165);
    (7/33), (-18/77), (25/77), (-4/231), (73/693), (85/693), (-388/1155);
    (-7/12), (9/28), (-25/84), (5/84), (-1/4), (-19/84), (59/105);
    (7/6), (-2/7), (5/42), (-5/21), (31/126), (29/126), (-26/105);
    (-7/4), (3/28), 0, (13/28), (-1/14), (-3/28), 0;
    1, 0, 0, (-2/7), 0, 0, 0;
    0, (-27/154), (25/77), (-31/154), (67/231), (41/231), (-92/385);
    0, (9/14), (-25/21), (9/14), (-17/21), (-65/63), (76/35);
    0, (-25/28), (25/21), (-25/28), (25/21), (145/126), (-94/35);
    0, (27/28), (-15/28), (27/28), (-29/28), (-13/14), (39/35);
    0, (-3/7), 0, (-3/7), (2/7), (3/7), 0;
    0, (-10/21), (25/21), (-10/21), (5/9), (20/21), (-64/35);
    0, (15/14), (-75/28), (15/14), (-155/84), (-5/3), (113/35);
    0, (-12/7), (10/7), (-12/7), (46/21), (6/7), (-8/7);
    0, 1, 0, 1, (-2/3), (-1/3), 0;
    0, 0, (25/14), 0, (15/14), (5/7), (-34/35);
    0, 0, (-5/2), 0, (-13/6), (-1/3), (2/5);
    0, 0, 1, 0, 1, 0, 0;
    0, 0, 0, (1/7), (-8/21), (-11/42), (16/35);
    0, 0, 0, (-10/21), (80/63), (10/7), (-328/105);
    0, 0, 0, (15/14), (-15/14), (-5/4), (117/35);
    0, 0, 0, (-12/7), (2/7), 1, (-48/35);
    0, 0, 0, 1, 0, (-1/2), 0;
    0, 0, 0, 0, (-25/21), (-15/7), (34/7);
    0, 0, 0, 0, (50/21), (65/21), (-296/35);
    0, 0, 0, 0, (-2/3), (-1), (16/5);
    0, 0, 0, 0, (-5/3), (-5/3), (14/5);
    0, 0, 0, 0, 1, 1, (-6/5);
    0, 0, 0, 0, 0, (20/21), (-16/7);
    0, 0, 0, 0, 0, (-5/3), (28/5);
    0, 0, 0, 0, 0, 1, (-12/5);
    0, 0, 0, 0, 0, 0, (-12/5);
    0, 0, 0, 0, 0, 0, 1]

theorem f415desc1_step : f415raise*f415desc0=f415desc1 := by
  refine natFourSparseRowProduct_matrix_check f415raise f415desc0 f415desc1
    f415raiseSparseRows f415_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 0) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 1) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 2) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 3) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 4) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 5) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 6) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 7) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 8) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 9) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 10) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 11) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 12) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 13) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 14) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 15) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 16) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 17) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 18) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 19) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 20) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 21) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 22) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 23) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 24) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 25) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 26) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 27) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 28) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 29) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 30) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 31) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 32) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 33) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 34) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 35) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 36) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 37) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 38) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 39) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 40) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 41) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 42) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 43) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 44) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 45) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 46) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 47) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 48) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 49) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 50) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 51) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 52) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 53) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 53 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 54) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 54 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 55) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 55 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 56) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 56 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 57) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 57 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 58) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 58 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 59) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 59 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 60) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 60 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 61) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 61 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 62) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 62 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f415raiseSparseRows 63) f415desc0 b)
      (fun (_ : Fin 1) (b : Fin 7) => f415desc1 63 b)
      (by decide +kernel) 0 b

theorem f415desc1_actual (x : Fin 7 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
      (natFourWordBlock f415basis (complexify b415relative *ᵥ x))=
      natFourWordBlock f416basis (complexify f415desc1 *ᵥ x) := by
  exact natFour_descendant_step 0
    (fun x => natFourWordBlock f415basis (complexify b415relative *ᵥ x))
    f415basis f416basis f415desc0 f415desc1 f415raise
    f415desc0_actual f415_actual_raise_block f415desc1_step x

#print axioms f415desc1_step
#print axioms f415desc1_actual
end TorusLean.BosonFiniteCertificate
