import torus.shared.BosonFiniteCertificateNatFourRaiseSparse411
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse412
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates405P11

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

def f405desc7 : Matrix (Fin 34) (Fin 1) ℚ :=
  !![(-1/6);
    (-8/3);
    (-5);
    (-8/3);
    (19/6);
    (16/3);
    (7/3);
    (-32/3);
    (-64/3);
    16;
    32;
    0;
    15;
    (320/3);
    (196/3);
    0;
    (224/3);
    (224/3);
    (35/3);
    (-28/3);
    0;
    (80/3);
    (-224/3);
    (-84);
    64;
    0;
    (-448);
    (-112);
    (-560/3);
    28;
    0;
    (-35);
    (1120/3);
    (280/3)]

theorem f405desc7_step : f411raise*f405desc6=f405desc7 := by
  refine natFourSparseRowProduct_matrix_check f411raise f405desc6 f405desc7
    f411raiseSparseRows f411_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 0) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 1) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 2) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 3) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 4) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 5) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 6) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 7) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 8) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 9) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 10) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 11) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 12) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 13) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 14) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 15) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 16) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 17) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 18) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 19) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 20) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 21) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 22) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 23) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 24) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 25) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 26) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 27) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 28) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 29) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 30) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 31) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 32) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 33) f405desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc7 33 b)
      (by decide +kernel) 0 b

theorem f405desc7_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7]
      (natFourWordBlock f405basis (complexify b405relative *ᵥ x))=
      natFourWordBlock f412basis (complexify f405desc7 *ᵥ x) := by
  exact natFour_descendant_step 6
    (fun x => natFourWordBlock f405basis (complexify b405relative *ᵥ x))
    f411basis f412basis f405desc6 f405desc7 f411raise
    f405desc6_actual f411_actual_raise_block f405desc7_step x

def f405desc8 : Matrix (Fin 39) (Fin 1) ℚ :=
  !![(-1/6);
    (-19/6);
    (-23/3);
    (-23/3);
    (1/2);
    (17/2);
    10;
    (-16);
    (-158/3);
    (-32/3);
    (163/3);
    (128/3);
    (14/3);
    (-19/3);
    (458/3);
    204;
    (196/3);
    (544/3);
    (868/3);
    (224/3);
    (329/3);
    (-20);
    (-148/3);
    (128/3);
    (-16);
    (-728/3);
    79;
    288;
    (-532);
    (-616);
    (-112/3);
    (-2912/3);
    (-175);
    92;
    84;
    (-518);
    (784/3);
    490;
    (2240/3)]

theorem f405desc8_step : f412raise*f405desc7=f405desc8 := by
  refine natFourSparseRowProduct_matrix_check f412raise f405desc7 f405desc8
    f412raiseSparseRows f412_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 0) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 1) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 2) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 3) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 4) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 5) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 6) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 7) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 8) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 9) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 10) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 11) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 12) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 13) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 14) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 15) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 16) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 17) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 18) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 19) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 20) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 21) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 22) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 23) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 24) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 25) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 26) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 27) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 28) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 29) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 30) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 31) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 32) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 33) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 34) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 35) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 36) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 37) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 38) f405desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc8 38 b)
      (by decide +kernel) 0 b

theorem f405desc8_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8]
      (natFourWordBlock f405basis (complexify b405relative *ᵥ x))=
      natFourWordBlock f413basis (complexify f405desc8 *ᵥ x) := by
  exact natFour_descendant_step 7
    (fun x => natFourWordBlock f405basis (complexify b405relative *ᵥ x))
    f412basis f413basis f405desc7 f405desc8 f412raise
    f405desc7_actual f412_actual_raise_block f405desc8_step x

#print axioms f405desc7_step
#print axioms f405desc7_actual
#print axioms f405desc8_step
#print axioms f405desc8_actual
end TorusLean.BosonFiniteCertificate
