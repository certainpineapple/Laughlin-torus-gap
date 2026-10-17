import torus.shared.BosonFiniteCertificateNatFourRaiseSparse411
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse412
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates404P11

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

def f404desc8 : Matrix (Fin 34) (Fin 2) ℚ :=
  !![(1/3), (-1/3);
    (20/3), (-20/3);
    (58/3), (-52/3);
    (100/3), (-52/3);
    (125/3), (43/3);
    (136/3), (200/3);
    (70/3), (140/3);
    (104/3), (-110/3);
    144, (-148);
    (488/3), (-248/3);
    144, 192;
    (448/3), (1400/3);
    86, (-116);
    (256/3), (-496/3);
    (392/3), (-224/3);
    112, (-28);
    (224/3), (-1064/3);
    560, (-1568);
    (490/3), (-1330/3);
    (112/3), (-148/3);
    56, (-162);
    (-512/3), (464/3);
    (-784/3), (1876/3);
    (-112), 420;
    (-432), 80;
    (-1568), 896;
    (-896), 952;
    (-896/3), (-784/3);
    (1400/3), (-3080/3);
    (-504), 280;
    (-784), 784;
    210, 140;
    (5600/3), (-1400/3);
    (1120/3), (-280/3)]

theorem f404desc8_step : f411raise*f404desc7=f404desc8 := by
  refine natFourSparseRowProduct_matrix_check f411raise f404desc7 f404desc8
    f411raiseSparseRows f411_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 0) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 1) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 2) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 3) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 4) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 5) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 6) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 7) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 8) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 9) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 10) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 11) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 12) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 13) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 14) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 15) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 16) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 17) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 18) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 19) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 20) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 21) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 22) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 23) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 24) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 25) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 26) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 27) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 28) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 29) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 30) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 31) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 32) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f411raiseSparseRows 33) f404desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc8 33 b)
      (by decide +kernel) 0 b

theorem f404desc8_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8]
      (natFourWordBlock f404basis (complexify b404relative *ᵥ x))=
      natFourWordBlock f412basis (complexify f404desc8 *ᵥ x) := by
  exact natFour_descendant_step 7
    (fun x => natFourWordBlock f404basis (complexify b404relative *ᵥ x))
    f411basis f412basis f404desc7 f404desc8 f411raise
    f404desc7_actual f411_actual_raise_block f404desc8_step x

def f404desc9 : Matrix (Fin 39) (Fin 2) ℚ :=
  !![(1/3), (-1/3);
    (23/3), (-23/3);
    26, (-24);
    (158/3), (-104/3);
    75, (-3);
    87, 81;
    92, 160;
    48, (-50);
    252, (-256);
    (1120/3), (-796/3);
    390, 138;
    384, 792;
    196, 560;
    230, (-264);
    420, (-480);
    360, (-48);
    504, 336;
    160, (-520);
    840, (-2352);
    672, (-1596);
    1050, (-2898);
    72, (-86);
    312, (-458);
    48, (-90);
    (-288), 972;
    (-336), 1932;
    (-234), (-360);
    (-2688), 1200;
    (-2856), 3024;
    (-1008), 1764;
    (-1792), 280;
    0, (-3192);
    630, (-1470);
    (-936), 360;
    (-3864), 2520;
    (-1260), 2016;
    0, 840;
    4620, (-1680);
    3360, (-840)]

theorem f404desc9_step : f412raise*f404desc8=f404desc9 := by
  refine natFourSparseRowProduct_matrix_check f412raise f404desc8 f404desc9
    f412raiseSparseRows f412_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 0) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 1) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 2) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 3) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 4) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 5) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 6) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 7) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 8) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 9) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 10) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 11) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 12) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 13) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 14) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 15) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 16) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 17) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 18) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 19) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 20) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 21) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 22) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 23) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 24) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 25) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 26) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 27) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 28) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 29) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 30) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 31) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 32) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 33) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 34) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 35) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 36) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 37) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f412raiseSparseRows 38) f404desc8 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc9 38 b)
      (by decide +kernel) 0 b

theorem f404desc9_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[9]
      (natFourWordBlock f404basis (complexify b404relative *ᵥ x))=
      natFourWordBlock f413basis (complexify f404desc9 *ᵥ x) := by
  exact natFour_descendant_step 8
    (fun x => natFourWordBlock f404basis (complexify b404relative *ᵥ x))
    f412basis f413basis f404desc8 f404desc9 f412raise
    f404desc8_actual f412_actual_raise_block f404desc9_step x

#print axioms f404desc8_step
#print axioms f404desc8_actual
#print axioms f404desc9_step
#print axioms f404desc9_actual
end TorusLean.BosonFiniteCertificate
