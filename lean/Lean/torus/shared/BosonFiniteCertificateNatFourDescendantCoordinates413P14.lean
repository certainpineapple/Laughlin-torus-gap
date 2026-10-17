import torus.shared.BosonFiniteCertificateNatFourRaiseSparse413
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates413P13

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

def f413desc1 : Matrix (Fin 47) (Fin 5) ℚ :=
  !![(-1/924), (1/792), (1/792), (-1/495), (-1/495);
    (5/462), (-5/396), (-5/396), (2/99), (2/99);
    (-41/924), (155/5544), (37/1848), (-89/3465), (-8/495);
    (25/231), (-53/2772), (-53/2772), (1/495), (-17/1386);
    (-11/84), (-1/72), (-1/168), (2/63), (1/45);
    (1/42), (2/63), (2/63), (-1/45), (-1/126);
    (5/28), (-1/56), (-1/56), 0, 0;
    (-1/7), 0, 0, 0, 0;
    (1/462), (59/2772), (9/308), (-184/3465), (-31/495);
    (-2/77), (-31/308), (-103/2772), (109/1155), (47/770);
    0, (1/84), (1/84), (1/15), (1/6);
    0, (5/28), (25/252), (-31/105), (-3/14);
    0, (-1/4), (-1/4), (1/5), (1/14);
    0, (1/7), (1/7), 0, 0;
    (1/7), (5/42), (-2/21), (1/105), (1/15);
    (-10/21), (5/252), (85/252), (-97/315), (-281/630);
    (15/14), (-15/28), (-25/84), (24/35), (2/5);
    (-12/7), (5/7), (1/3), (-16/35), (-4/35);
    1, (-1/2), (-1/6), 0, 0;
    0, (-25/84), (-25/84), (1/3), (61/210);
    0, (55/42), (5/14), (-106/105), (-37/105);
    0, (-1/6), (-1/6), (2/3), (1/15);
    0, (-5/3), 0, (7/15), (1/15);
    0, 1, 0, (-2/5), 0;
    (-2/77), (25/462), (-13/1386), (2/231), (13/231);
    (1/7), (-25/84), (-23/252), (19/105), (1/30);
    (-10/21), (55/126), (5/42), (-106/315), (-157/315);
    (15/14), (-5/14), (-5/21), (19/35), (37/70);
    (-12/7), (1/7), (11/21), (-12/35), (-6/35);
    1, 0, (-1/3), 0, 0;
    0, (5/12), (125/252), (-27/35), (-17/30);
    0, (-5/4), (-5/4), (9/5), (171/70);
    0, (15/14), (15/14), (-2), (-71/35);
    0, (-1/2), (-1/2), (6/5), (3/5);
    0, (20/21), (20/21), (-16/15), (-32/21);
    0, (-5/3), (-5/3), (8/3), (28/15);
    0, 1, 1, (-12/5), (-2/5);
    0, 0, 0, (2/5), (-2/5);
    0, 0, (-5/14), (27/35), (3/5);
    0, 0, (20/21), (-72/35), (-96/35);
    0, 0, (-5/3), (6/5), 2;
    0, 0, 1, 0, (-3/5);
    0, 0, 0, (8/5), (16/5);
    0, 0, 0, (-12/5), (-14/5);
    0, 0, 0, 1, 1;
    0, 0, 0, 0, (-8/5);
    0, 0, 0, 0, 1]

theorem f413desc1_step : f413raise*f413desc0=f413desc1 := by
  refine natFourSparseRowProduct_matrix_check f413raise f413desc0 f413desc1
    f413raiseSparseRows f413_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 0) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 1) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 2) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 3) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 4) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 5) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 6) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 7) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 8) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 9) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 10) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 11) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 12) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 13) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 14) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 15) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 16) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 17) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 18) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 19) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 20) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 21) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 22) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 23) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 24) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 25) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 26) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 27) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 28) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 29) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 30) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 31) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 32) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 33) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 34) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 35) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 36) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 37) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 38) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 39) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 40) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 41) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 42) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 43) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 44) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 45) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 5) => natFourSparseRowProduct (f413raiseSparseRows 46) f413desc0 b)
      (fun (_ : Fin 1) (b : Fin 5) => f413desc1 46 b)
      (by decide +kernel) 0 b

theorem f413desc1_actual (x : Fin 5 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
      (natFourWordBlock f413basis (complexify b413relative *ᵥ x))=
      natFourWordBlock f414basis (complexify f413desc1 *ᵥ x) := by
  exact natFour_descendant_step 0
    (fun x => natFourWordBlock f413basis (complexify b413relative *ᵥ x))
    f413basis f414basis f413desc0 f413desc1 f413raise
    f413desc0_actual f413_actual_raise_block f413desc1_step x

#print axioms f413desc1_step
#print axioms f413desc1_actual
end TorusLean.BosonFiniteCertificate
