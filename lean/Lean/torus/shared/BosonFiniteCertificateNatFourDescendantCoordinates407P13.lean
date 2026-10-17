import torus.shared.BosonFiniteCertificateNatFourRaiseSparse411
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse412
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates407P11

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

def f407desc5 : Matrix (Fin 34) (Fin 2) ℚ :=
  !![(1/20), (-1/15);
    (2/5), (-8/15);
    (1/5), (1/15);
    0, (4/3);
    (1/4), 1;
    (-2/5), (-4/5);
    (-3/5), (-13/15);
    (1/10), (-7/15);
    (-3), (10/3);
    0, (8/3);
    4, (-8/3);
    (-2), (-4/3);
    (-3), (1/3);
    0, (-32/3);
    (-4), (4/3);
    (-33/5), (142/15);
    0, (-16/3);
    0, 16;
    (5/2), (10/3);
    (-1), (2/3);
    (-3/2), (5/3);
    12, (-8);
    11, (-10/3);
    (3/5), (58/15);
    6, (-20/3);
    12, (-40/3);
    (-18), 20;
    4, (-24);
    20, (-160/3);
    (-6), (32/3);
    (-42), (172/3);
    (-15), (55/3);
    20, (-40/3);
    10, (-20/3)]

theorem f407desc5_step : f411raise*f407desc4=f407desc5 := by
  refine natFourSparseRowProduct_matrix_check f411raise f407desc4 f407desc5
    f411raiseSparseRows f411_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 0) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 1) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 2) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 3) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 4) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 5) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 6) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 7) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 8) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 9) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 10) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 11) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 12) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 13) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 14) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 15) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 16) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 17) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 18) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 19) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 20) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 21) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 22) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 23) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 24) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 25) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 26) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 27) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 28) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 29) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 30) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 31) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 32) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 33) f407desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc5 33 b)
      (by decide +kernel) 0 b

theorem f407desc5_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
      (natFourWordBlock f407basis (complexify b407relative *ᵥ x))=
      natFourWordBlock f412basis (complexify f407desc5 *ᵥ x) := by
  exact natFour_descendant_step 4
    (fun x => natFourWordBlock f407basis (complexify b407relative *ᵥ x))
    f411basis f412basis f407desc4 f407desc5 f411raise
    f407desc4_actual f411_actual_raise_block f407desc5_step x

def f407desc6 : Matrix (Fin 39) (Fin 2) ℚ :=
  !![(1/20), (-1/15);
    (11/20), (-11/15);
    (3/5), (-7/15);
    (1/5), (7/5);
    (1/4), (7/3);
    (-3/20), (1/5);
    (-8/5), (-38/15);
    (9/10), (-23/15);
    (-12/5), (38/15);
    (-3), (26/3);
    (9/2), 2;
    (6/5), (-28/5);
    (-16/5), (-46/15);
    (-6), (11/3);
    (-6), (-22/3);
    0, (-12);
    (-96/5), (284/15);
    0, (-16);
    (-4), (20/3);
    (-33/5), (382/15);
    (15/2), 26;
    (-9/10), (1/5);
    (-15/2), 7;
    (21/2), (-11/3);
    27, (-14);
    (51/5), (46/15);
    0, (-3);
    48, (-160/3);
    12, (4/3);
    (-117/5), (186/5);
    16, (-128/3);
    30, (-356/3);
    (45/2), (-50);
    0, 4;
    (-48), 76;
    (-90), 114;
    (-60), (232/3);
    30, (-130/3);
    60, (-40)]

theorem f407desc6_step : f412raise*f407desc5=f407desc6 := by
  refine natFourSparseRowProduct_matrix_check f412raise f407desc5 f407desc6
    f412raiseSparseRows f412_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 0) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 1) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 2) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 3) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 4) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 5) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 6) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 7) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 8) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 9) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 10) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 11) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 12) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 13) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 14) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 15) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 16) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 17) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 18) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 19) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 20) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 21) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 22) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 23) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 24) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 25) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 26) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 27) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 28) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 29) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 30) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 31) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 32) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 33) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 34) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 35) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 36) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 37) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 38) f407desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc6 38 b)
      (by decide +kernel) 0 b

theorem f407desc6_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6]
      (natFourWordBlock f407basis (complexify b407relative *ᵥ x))=
      natFourWordBlock f413basis (complexify f407desc6 *ᵥ x) := by
  exact natFour_descendant_step 5
    (fun x => natFourWordBlock f407basis (complexify b407relative *ᵥ x))
    f412basis f413basis f407desc5 f407desc6 f412raise
    f407desc5_actual f412_actual_raise_block f407desc6_step x

#print axioms f407desc5_step
#print axioms f407desc5_actual
#print axioms f407desc6_step
#print axioms f407desc6_actual
end TorusLean.BosonFiniteCertificate
