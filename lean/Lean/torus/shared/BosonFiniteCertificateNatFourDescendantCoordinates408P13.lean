import torus.shared.BosonFiniteCertificateNatFourRaiseSparse411
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse412
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates408P11

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

def f408desc4 : Matrix (Fin 34) (Fin 4) ℚ :=
  !![(1/35), (-1/35), (-1/35), (1/21);
    (4/35), (-4/35), (-4/35), (4/21);
    (2/5), (1/10), (1/5), (-2/5);
    (4/7), (-1/14), (23/70), (-68/105);
    (-3/7), (-4/7), (1/35), (23/105);
    (-8/35), (-19/70), (9/70), (24/35);
    (2/5), (1/10), (1/5), (4/15);
    (-4/5), (3/10), (1/5), (-4/15);
    (8/35), (89/70), (47/70), (-128/105);
    (-8/35), (-19/70), (-103/70), (184/105);
    (-192/35), (-1/70), (-141/70), (32/21);
    (16/5), (23/10), (-1/10), (-56/15);
    (162/35), (-9/70), (-36/35), (208/105);
    (64/35), (-29/35), (-29/35), (64/21);
    (-16/5), (-14/5), (6/5), (-4);
    (24/5), (-33/10), (-3/10), (-8/3);
    (-32/5), (7/5), (17/5), (-8/3);
    0, (1/2), (-3/2), (16/3);
    2, 1, (-2), 4;
    (-72/35), (2/35), (9/35), (-8/35);
    (-12/35), (-93/35), (-81/70), (44/21);
    (-32/7), (4/7), (-8/35), (32/35);
    (-24/5), (43/10), (21/10), (-8/15);
    (24/5), (6/5), (3/5), (16/15);
    (432/35), (-117/35), (-33/35), (32/105);
    (-64/5), (59/5), (63/5), (-96/5);
    (48/5), (-141/10), (-9/2), (88/5);
    (-64/5), (44/5), 8, (-272/15);
    8, (3/2), (-1/2), (-32/3);
    (24/5), (6/5), (-6/5), (-16/15);
    (-48/5), (-12/5), (-12), (256/15);
    6, (-27/2), (-12), (70/3);
    0, 4, 6, (-8);
    0, 4, 6, (-8)]

theorem f408desc4_step : f411raise*f408desc3=f408desc4 := by
  refine natFourSparseRowProduct_matrix_check f411raise f408desc3 f408desc4
    f411raiseSparseRows f411_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 0) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 1) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 2) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 3) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 4) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 5) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 6) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 7) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 8) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 9) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 10) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 11) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 12) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 13) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 14) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 15) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 16) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 17) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 18) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 19) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 20) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 21) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 22) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 23) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 24) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 25) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 26) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 27) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 28) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 29) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 30) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 31) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 32) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f411raiseSparseRows 33) f408desc3 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc4 33 b)
      (by decide +kernel) 0 b

theorem f408desc4_actual (x : Fin 4 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
      (natFourWordBlock f408basis (complexify b408relative *ᵥ x))=
      natFourWordBlock f412basis (complexify f408desc4 *ᵥ x) := by
  exact natFour_descendant_step 3
    (fun x => natFourWordBlock f408basis (complexify b408relative *ᵥ x))
    f411basis f412basis f408desc3 f408desc4 f411raise
    f408desc3_actual f411_actual_raise_block f408desc4_step x

def f408desc5 : Matrix (Fin 39) (Fin 4) ℚ :=
  !![(1/35), (-1/35), (-1/35), (1/21);
    (1/5), (-1/5), (-1/5), (1/3);
    (18/35), (-1/70), (3/35), (-22/105);
    (34/35), (1/35), (37/70), (-22/21);
    (1/7), (-9/14), (5/14), (-3/7);
    (-23/35), (-59/70), (11/70), (19/21);
    (4/7), (-1/14), (37/70), (128/105);
    (-4/7), (1/14), (-1/35), (4/35);
    (-4/7), (29/14), (103/70), (-268/105);
    (8/7), (6/7), (-1/7), (-16/21);
    (-46/7), (-10/7), (-24/7), (26/7);
    (-96/35), (61/35), (-13/7), (-88/105);
    4, (5/2), (3/10), (-16/5);
    (34/7), (8/7), (-5/14), (16/21);
    (76/7), (-19/14), (-61/14), (184/21);
    (-48/7), (-51/14), (-23/14), (4/7);
    (48/5), (-71/10), (1/2), (-196/15);
    (-32/7), (4/7), (18/7), (8/21);
    (-16), (1/2), (13/2), (-4);
    (24/5), (-14/5), (-9/5), (8/3);
    6, (7/2), (-15/2), (52/3);
    (-20/7), (5/14), (16/35), (-52/105);
    (-44/7), (-17/14), (2/7), (4/21);
    (-36/7), (-33/14), (-20/7), (100/21);
    (-104/7), (34/7), (-1/7), (40/21);
    8, 9, (16/5), (-32/15);
    (114/7), (-123/14), (-30/7), (136/21);
    (32/7), (38/7), (66/7), (-96/7);
    (-16), (7/2), (27/2), (-20/3);
    24, (-15), (-18/5), (256/15);
    (-32), 22, 24, (-40);
    0, 7, 9, (-104/3);
    10, (5/2), (-5/2), (-20/3);
    (120/7), (-15/7), (-15/7), (-16/21);
    (-8), 13, (-3), (-16/3);
    12, (-87/2), (-81/2), (244/3);
    (-32), 8, (-10), 8;
    20, (-35/2), (-25/2), 20;
    0, 20, 30, (-40)]

theorem f408desc5_step : f412raise*f408desc4=f408desc5 := by
  refine natFourSparseRowProduct_matrix_check f412raise f408desc4 f408desc5
    f412raiseSparseRows f412_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 0) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 1) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 2) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 3) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 4) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 5) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 6) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 7) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 8) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 9) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 10) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 11) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 12) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 13) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 14) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 15) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 16) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 17) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 18) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 19) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 20) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 21) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 22) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 23) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 24) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 25) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 26) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 27) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 28) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 29) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 30) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 31) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 32) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 33) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 34) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 35) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 36) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 37) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 4) => natFourSparseRowProduct (f412raiseSparseRows 38) f408desc4 b)
      (fun (_ : Fin 1) (b : Fin 4) => f408desc5 38 b)
      (by decide +kernel) 0 b

theorem f408desc5_actual (x : Fin 4 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
      (natFourWordBlock f408basis (complexify b408relative *ᵥ x))=
      natFourWordBlock f413basis (complexify f408desc5 *ᵥ x) := by
  exact natFour_descendant_step 4
    (fun x => natFourWordBlock f408basis (complexify b408relative *ᵥ x))
    f412basis f413basis f408desc4 f408desc5 f412raise
    f408desc4_actual f412_actual_raise_block f408desc5_step x

#print axioms f408desc4_step
#print axioms f408desc4_actual
#print axioms f408desc5_step
#print axioms f408desc5_actual
end TorusLean.BosonFiniteCertificate
