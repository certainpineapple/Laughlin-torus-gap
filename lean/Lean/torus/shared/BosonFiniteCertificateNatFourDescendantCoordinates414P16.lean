import torus.shared.BosonFiniteCertificateNatFourRaiseSparse415
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates414P15

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

def f414desc2 : Matrix (Fin 64) (Fin 8) ℚ :=
  !![(-1/1716), (1/1716), (-1/1287), (1/1716), (-1/1287), (-1/1287), (1/715), (1/715);
    (2/429), (-2/429), (8/1287), (-2/429), (8/1287), (8/1287), (-8/715), (-8/715);
    (-1/26), (4/273), (-19/1638), (25/2002), (-46/9009), (-53/18018), (1/715), (-7/4290);
    (49/429), (-19/1001), (-58/9009), (-10/429), (-193/36036), (-5/1001), (304/15015), (356/15015);
    (-7/33), (-1/462), (37/1386), (-1/231), (4/231), (8/693), (-58/3465), (-2/231);
    (7/33), (23/462), (-5/462), (23/462), (-19/2772), (-5/462), (-26/3465), (-16/1155);
    0, (-1/21), (-1/63), (-1/21), (-1/126), (-1/126), (4/315), (1/210);
    (-1/3), (-1/42), (1/126), (-1/42), (1/126), (1/126), 0, 0;
    (1/4), (1/28), 0, (1/28), 0, 0, 0, 0;
    (25/858), (-16/3003), (-5/6006), (-19/6006), (-2/273), (-19/2002), (3/143), (103/4290);
    (-70/429), (61/3003), (185/9009), (139/3003), (-71/3276), (-46/1287), (54/1001), (309/5005);
    (7/11), (-5/77), (20/231), (-4/231), (185/2772), (7/99), (-584/3465), (-32/165);
    (-49/33), (37/462), (-25/154), (7/66), (-281/2772), (-61/1386), (38/495), (4/165);
    (7/3), (-1/6), (1/42), (-1/6), (-1/252), (5/126), (34/315), (17/105);
    (-7/3), (1/6), (1/6), (1/6), (11/126), (11/126), (-8/63), (-1/21);
    1, (-1/14), (-1/14), (-1/14), (-1/14), (-1/14), 0, 0;
    (-7/66), (-17/462), (-32/693), (-59/462), (83/1386), (11/126), (-41/385), (-81/770);
    (14/33), (15/77), (-125/693), (41/231), (-100/693), (-1/7), (104/495), (74/385);
    (-7/6), (2/21), (59/126), (-13/42), (1/14), (-8/63), (31/315), (19/105);
    (7/3), (-1/7), (-10/63), (-2/21), (7/36), (8/63), (-104/315), (-13/35);
    (-7/2), (3/7), (-9/14), (11/14), (-3/14), (-4/21), (9/35), (3/35);
    2, (-2/7), (2/7), (-4/7), (1/7), (2/21), 0, 0;
    0, (-1/3), (2/9), (1/3), (1/21), (-1/63), (2/45), (4/35);
    0, (5/42), (-55/126), (-25/42), (5/36), (55/126), (-32/63), (-62/105);
    0, (-9/14), (1/14), (9/14), (-23/42), (-5/14), (58/105), (2/5);
    0, (2/7), (20/21), (-2/7), (1/7), (4/21), (-4/15), (-2/35);
    0, (15/14), (-5/14), 0, (-5/21), (-5/21), (38/105), (11/35);
    0, (-12/7), (10/7), 0, (37/42), (2/21), (-8/15), (-6/35);
    0, 1, (-8/3), 0, (-1/3), 0, (2/15), 0;
    0, 0, 1, 0, (-1/6), 0, (2/15), 0;
    (7/429), (94/3003), (-173/3003), (29/3003), (-3/182), (-25/9009), (62/15015), (-107/15015);
    (-7/66), (-25/231), (299/1386), (-29/462), (5/36), (157/1386), (-251/1155), (-31/154);
    (14/33), (8/33), (-38/231), (2/77), (-7/99), (-86/693), (964/3465), (142/385);
    (-7/6), (-13/42), (-5/21), (-1/21), (1/28), (-1/63), (1/21), (17/210);
    (7/3), (-2/21), (3/7), (-1/7), (17/126), (-1/63), (-106/315), (-17/35);
    (-7/2), (11/14), (-1/7), (3/7), (-3/14), (-5/21), (11/35), (9/70);
    2, (-4/7), 0, (-2/7), (1/7), (4/21), 0, 0;
    0, (-1/7), (-1/21), (5/77), (-8/33), (-169/693), (76/165), (172/385);
    0, (13/21), (-5/63), (-1/21), (-4/21), (1/7), (-8/45), (-2/5);
    0, (-25/42), (155/126), (25/42), (25/42), (115/126), (-94/63), (-51/35);
    0, (9/14), (-25/14), (-9/14), (-31/28), (-9/14), (64/35), (81/35);
    0, (-2/7), (4/7), (2/7), (3/7), (8/21), (-44/35), (-18/35);
    0, (-20/21), (10/63), (-20/21), (5/9), (20/63), (-268/315), (-104/105);
    0, (15/7), (-15/7), (15/7), (-115/84), (-15/7), (358/105), (132/35);
    0, (-24/7), 4, (-24/7), (8/3), (44/21), (-296/105), (-92/35);
    0, 2, (-4/3), 2, (-1), (-4/3), (4/3), (2/5);
    0, 0, (10/7), 0, (5/14), (10/7), (-64/35), (-74/35);
    0, 0, (-4), 0, (-11/6), (-2/3), (28/15), (6/5);
    0, 0, 2, 0, 1, 0, (-4/5), 0;
    0, (1/7), (-8/21), (2/7), (1/21), (-1/63), (-2/15), (-1/7);
    0, (-10/21), (80/63), (-20/21), (20/21), (50/63), (-52/45), (-6/7);
    0, (15/14), (-15/14), (15/7), (-10/7), (-65/42), (102/35), (177/70);
    0, (-12/7), (2/7), (-24/7), (11/7), (34/21), (-76/35), (-102/35);
    0, 1, 0, 2, (-1), (-1), (6/5), (3/5);
    0, 0, (-25/21), 0, (-15/7), (-40/21), (374/105), (128/35);
    0, 0, (50/21), 0, (85/21), (10/3), (-1028/105), (-346/35);
    0, 0, (-2/3), 0, (-1), (-2/3), (52/15), 6;
    0, 0, (-5/3), 0, (-10/3), (-10/3), (86/15), 6;
    0, 0, 1, 0, 2, 2, (-14/5), (-18/5);
    0, 0, 0, 0, (20/21), (40/21), (-32/15), (-88/35);
    0, 0, 0, 0, (-5/3), (-10/3), (104/15), (38/5);
    0, 0, 0, 0, 1, 2, (-24/5), (-26/5);
    0, 0, 0, 0, 0, 0, (-8/5), (-16/5);
    0, 0, 0, 0, 0, 0, 1, 2]

theorem f414desc2_step : f415raise*f414desc1=f414desc2 := by
  refine natFourSparseRowProduct_matrix_check f415raise f414desc1 f414desc2
    f415raiseSparseRows f415_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 0) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 1) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 2) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 3) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 4) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 5) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 6) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 7) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 8) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 9) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 10) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 11) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 12) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 13) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 14) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 15) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 16) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 17) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 18) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 19) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 20) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 21) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 22) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 23) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 24) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 25) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 26) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 27) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 28) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 29) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 30) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 31) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 32) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 33) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 34) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 35) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 36) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 37) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 38) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 39) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 40) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 41) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 42) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 43) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 44) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 45) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 46) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 47) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 48) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 49) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 50) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 51) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 52) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 53) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 53 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 54) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 54 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 55) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 55 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 56) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 56 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 57) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 57 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 58) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 58 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 59) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 59 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 60) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 60 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 61) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 61 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 62) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 62 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f415raiseSparseRows 63) f414desc1 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc2 63 b)
      (by decide +kernel) 0 b

theorem f414desc2_actual (x : Fin 8 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
      (natFourWordBlock f414basis (complexify b414relative *ᵥ x))=
      natFourWordBlock f416basis (complexify f414desc2 *ᵥ x) := by
  exact natFour_descendant_step 1
    (fun x => natFourWordBlock f414basis (complexify b414relative *ᵥ x))
    f415basis f416basis f414desc1 f414desc2 f415raise
    f414desc1_actual f415_actual_raise_block f414desc2_step x

#print axioms f414desc2_step
#print axioms f414desc2_actual
end TorusLean.BosonFiniteCertificate
