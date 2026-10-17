import torus.shared.BosonFiniteCertificateNatFourRaiseSparse411
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse412
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates403P11

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

def f403desc9 : Matrix (Fin 34) (Fin 1) ℚ :=
  !![(1/2);
    12;
    39;
    60;
    (45/2);
    (-72);
    (-63);
    84;
    456;
    504;
    (-144);
    (-1008);
    459;
    288;
    (-1764);
    (-1512);
    (-1008);
    (-5040);
    (-1155);
    172;
    1188;
    1008;
    (-504);
    (-756);
    2160;
    2016;
    (-3024);
    (-1008);
    (-2520);
    1260;
    3024;
    945;
    5040;
    840]

theorem f403desc9_step : f411raise*f403desc8=f403desc9 := by
  refine natFourSparseRowProduct_matrix_check f411raise f403desc8 f403desc9
    f411raiseSparseRows f411_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 0) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 1) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 2) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 3) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 4) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 5) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 6) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 7) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 8) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 9) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 10) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 11) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 12) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 13) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 14) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 15) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 16) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 17) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 18) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 19) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 20) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 21) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 22) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 23) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 24) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 25) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 26) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 27) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 28) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 29) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 30) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 31) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 32) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f411raiseSparseRows 33) f403desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc9 33 b)
      (by decide +kernel) 0 b

theorem f403desc9_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[9]
      (natFourWordBlock f403basis (complexify b403relative *ᵥ x))=
      natFourWordBlock f412basis (complexify f403desc9 *ᵥ x) := by
  exact natFour_descendant_step 8
    (fun x => natFourWordBlock f403basis (complexify b403relative *ᵥ x))
    f411basis f412basis f403desc8 f403desc9 f411raise
    f403desc8_actual f411_actual_raise_block f403desc9_step x

def f403desc10 : Matrix (Fin 39) (Fin 1) ℚ :=
  !![(1/2);
    (27/2);
    51;
    99;
    (165/2);
    (-99/2);
    (-198);
    108;
    702;
    1080;
    405;
    (-1296);
    (-1134);
    915;
    1710;
    (-1620);
    (-5796);
    (-720);
    (-8820);
    (-6552);
    (-8505);
    256;
    2160;
    2700;
    360;
    (-3024);
    4995;
    8640;
    (-3780);
    (-6048);
    0;
    (-15120);
    (-3675);
    3420;
    8820;
    1890;
    10080;
    9450;
    8400]

theorem f403desc10_step : f412raise*f403desc9=f403desc10 := by
  refine natFourSparseRowProduct_matrix_check f412raise f403desc9 f403desc10
    f412raiseSparseRows f412_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 0) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 1) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 2) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 3) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 4) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 5) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 6) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 7) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 8) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 9) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 10) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 11) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 12) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 13) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 14) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 15) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 16) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 17) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 18) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 19) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 20) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 21) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 22) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 23) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 24) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 25) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 26) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 27) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 28) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 29) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 30) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 31) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 32) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 33) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 34) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 35) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 36) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 37) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f412raiseSparseRows 38) f403desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc10 38 b)
      (by decide +kernel) 0 b

theorem f403desc10_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[10]
      (natFourWordBlock f403basis (complexify b403relative *ᵥ x))=
      natFourWordBlock f413basis (complexify f403desc10 *ᵥ x) := by
  exact natFour_descendant_step 9
    (fun x => natFourWordBlock f403basis (complexify b403relative *ᵥ x))
    f412basis f413basis f403desc9 f403desc10 f412raise
    f403desc9_actual f412_actual_raise_block f403desc10_step x

#print axioms f403desc9_step
#print axioms f403desc9_actual
#print axioms f403desc10_step
#print axioms f403desc10_actual
end TorusLean.BosonFiniteCertificate
