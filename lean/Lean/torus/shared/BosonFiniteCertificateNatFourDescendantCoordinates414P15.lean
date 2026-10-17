import torus.shared.BosonFiniteCertificateNatFourRaiseSparse414
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates414P14

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

def f414desc1 : Matrix (Fin 54) (Fin 8) ℚ :=
  !![(-1/1716), (1/1716), (-1/1287), (1/1716), (-1/1287), (-1/1287), (1/715), (1/715);
    (1/156), (-1/156), (1/117), (-1/156), (1/117), (1/117), (-1/65), (-1/65);
    (-7/156), (23/1092), (-11/546), (227/12012), (-41/3003), (-23/2002), (12/715), (59/4290);
    (7/44), (-37/924), (19/1386), (-13/308), (23/2772), (1/154), (4/1155), (23/2310);
    (-49/132), (5/132), (1/77), (5/132), (25/2772), (1/198), (-2/99), (-43/2310);
    (7/12), (1/84), (-1/42), (1/84), (-1/63), (-1/63), (4/315), (1/210);
    (-7/12), (-5/84), (1/126), (-5/84), (1/126), (1/126), 0, 0;
    (1/4), (1/28), 0, (1/28), 0, 0, 0, 0;
    (7/429), (15/2002), (-323/18018), (29/3003), (-20/819), (-479/18018), (37/715), (47/858);
    (-7/66), (-17/462), (67/693), (-5/462), (151/2772), (4/99), (-32/385), (-29/385);
    (14/33), (4/77), (-26/693), (6/77), (-1/231), (4/231), (-64/693), (-32/231);
    (-7/6), (-1/21), (-19/126), (-1/21), (-29/252), (-1/14), (22/105), (1/5);
    (7/3), (-1/7), (2/9), (-1/7), (1/7), (1/7), (-8/63), (-1/21);
    (-7/2), (3/7), (-1/14), (3/7), (-1/14), (-1/14), 0, 0;
    2, (-2/7), 0, (-2/7), 0, 0, 0, 0;
    0, 0, (-1/7), (-9/77), (5/924), (65/1386), (-9/385), (-23/770);
    0, (1/7), (1/7), (1/3), (-19/126), (-16/63), (22/63), (41/105);
    0, 0, (10/21), (-25/42), (85/252), (25/126), (-29/63), (-43/105);
    0, 0, (-6/7), (9/14), (-2/7), (-3/14), (9/35), (3/35);
    0, 0, (2/7), (-2/7), (1/7), (2/21), 0, 0;
    0, (-10/21), (5/63), 0, (25/126), (5/21), (-32/105), (-29/105);
    0, (15/14), (-15/14), 0, (-25/42), (-5/21), (59/105), (13/35);
    0, (-12/7), 2, 0, (1/3), (2/21), (-4/15), (-2/35);
    0, 1, (-2/3), 0, (-1/6), 0, 0, 0;
    0, 0, (5/7), 0, (5/14), 0, (-1/5), (-2/35);
    0, 0, (-2), 0, (-1/6), 0, (2/15), 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, (1/42), (-5/126), 0, (1/126), (1/42), (-1/21), (-13/210);
    0, (-1/7), (5/21), (-4/77), (2/33), (1/693), (2/231), (23/385);
    0, (1/3), (-23/63), 0, (-8/63), (-1/7), (38/105), (47/105);
    0, (-25/42), (5/18), 0, (5/18), (25/126), (-11/21), (-17/30);
    0, (9/14), (-1/14), 0, (-2/7), (-5/14), (11/35), (9/70);
    0, (-2/7), 0, 0, (1/7), (4/21), 0, 0;
    0, (1/7), (-8/21), (2/7), (-31/84), (-37/126), (7/15), (5/14);
    0, (-10/21), (80/63), (-20/21), (20/21), (80/63), (-688/315), (-12/5);
    0, (15/14), (-15/14), (15/7), (-5/4), (-20/21), (11/5), (87/35);
    0, (-12/7), (2/7), (-24/7), 1, (26/21), (-44/35), (-18/35);
    0, 1, 0, 2, (-1/2), (-2/3), 0, 0;
    0, 0, (-25/21), 0, (-25/42), (-25/21), (172/105), (59/35);
    0, 0, (50/21), 0, (5/3), (10/7), (-92/35), (-86/35);
    0, 0, (-2/3), 0, (-1/3), (-2/3), (4/3), (2/5);
    0, 0, (-5/3), 0, (-5/3), 0, 1, (2/5);
    0, 0, 1, 0, 1, 0, (-4/5), 0;
    0, 0, 0, 0, (5/12), (5/18), (-3/5), (-1/2);
    0, 0, 0, 0, (-5/4), (-55/42), (99/35), (213/70);
    0, 0, 0, 0, (15/14), (5/7), (-74/35), (-3);
    0, 0, 0, 0, (-1/2), (-1/3), (6/5), (3/5);
    0, 0, 0, 0, (20/21), (40/21), (-56/15), (-144/35);
    0, 0, 0, 0, (-5/3), (-10/3), (68/15), (34/5);
    0, 0, 0, 0, 1, 2, (-12/5), (-6/5);
    0, 0, 0, 0, 0, 0, (1/5), (-6/5);
    0, 0, 0, 0, 0, 0, (8/5), (8/5);
    0, 0, 0, 0, 0, 0, (-12/5), (-4);
    0, 0, 0, 0, 0, 0, 1, 2]

theorem f414desc1_step : f414raise*f414desc0=f414desc1 := by
  refine natFourSparseRowProduct_matrix_check f414raise f414desc0 f414desc1
    f414raiseSparseRows f414_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 0) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 1) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 2) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 3) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 4) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 5) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 6) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 7) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 8) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 9) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 10) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 11) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 12) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 13) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 14) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 15) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 16) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 17) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 18) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 19) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 20) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 21) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 22) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 23) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 24) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 25) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 26) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 27) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 28) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 29) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 30) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 31) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 32) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 33) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 34) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 35) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 36) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 37) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 38) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 39) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 40) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 41) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 42) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 43) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 44) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 45) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 46) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 47) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 48) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 49) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 50) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 51) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 52) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 8) => natFourSparseRowProduct (f414raiseSparseRows 53) f414desc0 b)
      (fun (_ : Fin 1) (b : Fin 8) => f414desc1 53 b)
      (by decide +kernel) 0 b

theorem f414desc1_actual (x : Fin 8 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
      (natFourWordBlock f414basis (complexify b414relative *ᵥ x))=
      natFourWordBlock f415basis (complexify f414desc1 *ᵥ x) := by
  exact natFour_descendant_step 0
    (fun x => natFourWordBlock f414basis (complexify b414relative *ᵥ x))
    f414basis f415basis f414desc0 f414desc1 f414raise
    f414desc0_actual f414_actual_raise_block f414desc1_step x

#print axioms f414desc1_step
#print axioms f414desc1_actual
end TorusLean.BosonFiniteCertificate
