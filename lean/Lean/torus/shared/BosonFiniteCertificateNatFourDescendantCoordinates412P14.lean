import torus.shared.BosonFiniteCertificateNatFourRaiseSparse413
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates412P13

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

def f412desc2 : Matrix (Fin 47) (Fin 7) ℚ :=
  !![(1/462), (-1/462), (1/330), (-1/462), (1/330), (1/330), (-1/165);
    (-1/77), (1/77), (-1/55), (1/77), (-1/55), (-1/55), (2/55);
    (15/154), (-2/77), (17/770), (-25/1386), (-2/1155), (-67/6930), (3/110);
    (-50/231), (1/462), (46/1155), (25/1386), (27/770), (116/3465), (-92/1155);
    (11/42), (1/21), (-13/210), (1/18), (-1/35), (-1/126), (-1/210);
    (-1/21), (-1/14), (-1/105), (-1/14), (-1/42), (-1/105), (1/21);
    (-5/14), (-1/42), (3/70), (-1/42), (1/70), (1/70), 0;
    (2/7), (1/21), 0, (1/21), 0, 0, 0;
    (-1/11), (3/154), (-1/77), (8/693), (5/462), (13/693), (-1/22);
    (32/77), (-9/154), (4/385), (-191/1386), (277/2310), (542/3465), (-118/385);
    (-4/3), (1/6), (-4/15), (1/42), (-41/210), (-22/105), (10/21);
    (50/21), (-5/42), (26/105), (-25/126), (1/10), (-4/63), (4/21);
    (-18/7), (3/14), (6/35), (3/14), (17/70), (4/35), (-3/7);
    (8/7), (-2/21), (-12/35), (-2/21), (-4/35), (-4/35), 0;
    (2/7), (1/14), (1/35), (17/63), (-29/210), (-52/315), (19/70);
    (-20/21), (-5/14), (52/105), (-5/42), (29/210), (2/35), (-8/105);
    (15/7), (-10/21), (-3/5), 0, (4/35), (7/15), (-27/35);
    (-24/7), (10/21), (-12/35), (6/7), (-4/7), (-4/15), (24/35);
    2, (-1/3), (6/5), (-2/3), (1/5), (2/15), 0;
    0, (25/42), (-2/7), (-25/42), (1/10), (26/105), (-19/35);
    0, (5/21), (-4/35), (5/7), (-19/35), (-16/21), (44/35);
    0, (1/3), (-8/5), (-1/3), (3/5), (4/15), (-2/5);
    0, (-5/3), (13/5), 0, (3/5), (2/15), (-2/5);
    0, 1, (-6/5), 0, (-3/5), 0, 0;
    (-4/77), (-1/11), (12/77), (-19/693), (59/1155), (8/495), (-2/77);
    (2/7), (3/14), (-2/5), (19/126), (-71/210), (-20/63), (23/35);
    (-20/21), (-5/21), (4/105), (5/63), (1/35), (16/63), (-62/105);
    (15/7), 0, (27/35), (-5/42), (1/7), (1/3), (-51/70);
    (-24/7), (6/7), (-24/35), (10/21), (-18/35), (-32/105), (36/35);
    2, (-2/3), 0, (-1/3), (1/5), (4/15), 0;
    0, (5/14), (-6/35), (-5/42), (5/14), (38/105), (-27/35);
    0, (-55/42), (36/35), (-5/42), (87/70), (58/105), (-6/5);
    0, (5/7), (-96/35), (-5/7), (-59/35), (-12/5), (156/35);
    0, (-1/3), (12/5), (1/3), (7/5), (8/15), (-18/5);
    0, (40/21), (-32/35), (40/21), (-48/35), (-48/35), (16/5);
    0, (-10/3), 4, (-10/3), (12/5), 4, (-34/5);
    0, 2, (-24/5), 2, (-14/5), (-8/5), (12/5);
    0, 0, (6/5), 0, (4/5), (-4/5), (12/5);
    0, (-5/14), (27/35), (-5/7), (3/70), (6/35), (-9/70);
    0, (20/21), (-72/35), (40/21), (-12/5), (-208/105), (132/35);
    0, (-5/3), (6/5), (-10/3), (17/5), (52/15), (-27/5);
    0, 1, 0, 2, (-6/5), (-6/5), (18/5);
    0, 0, (8/5), 0, (16/5), (16/5), (-8);
    0, 0, (-12/5), 0, (-22/5), (-4), (42/5);
    0, 0, 1, 0, 2, 2, (-6);
    0, 0, 0, 0, (-8/5), (-16/5), (32/5);
    0, 0, 0, 0, 1, 2, (-3)]

theorem f412desc2_step : f413raise*f412desc1=f412desc2 := by
  refine natFourSparseRowProduct_matrix_check f413raise f412desc1 f412desc2
    f413raiseSparseRows f413_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 0) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 1) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 2) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 3) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 4) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 5) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 6) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 7) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 8) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 9) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 10) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 11) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 12) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 13) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 14) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 15) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 16) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 17) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 18) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 19) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 20) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 21) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 22) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 23) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 24) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 25) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 26) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 27) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 28) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 29) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 30) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 31) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 32) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 33) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 34) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 35) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 36) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 37) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 38) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 39) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 40) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 41) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 42) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 43) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 44) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 45) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 7) => natFourSparseRowProduct (f413raiseSparseRows 46) f412desc1 b)
      (fun (_ : Fin 1) (b : Fin 7) => f412desc2 46 b)
      (by decide +kernel) 0 b

theorem f412desc2_actual (x : Fin 7 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
      (natFourWordBlock f412basis (complexify b412relative *ᵥ x))=
      natFourWordBlock f414basis (complexify f412desc2 *ᵥ x) := by
  exact natFour_descendant_step 1
    (fun x => natFourWordBlock f412basis (complexify b412relative *ᵥ x))
    f413basis f414basis f412desc1 f412desc2 f413raise
    f412desc1_actual f413_actual_raise_block f412desc2_step x

#print axioms f412desc2_step
#print axioms f412desc2_actual
end TorusLean.BosonFiniteCertificate
