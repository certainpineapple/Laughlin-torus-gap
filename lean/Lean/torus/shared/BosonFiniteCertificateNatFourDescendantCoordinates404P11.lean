import torus.shared.BosonFiniteCertificateNatFourRaiseSparse407
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse408
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse409
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse410
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates404P07

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

def f404desc4 : Matrix (Fin 15) (Fin 2) ℚ :=
  !![(1/3), (-1/3);
    (8/3), (-8/3);
    (8/3), (-2/3);
    (8/3), (16/3);
    (5/3), (13/3);
    (4/3), (-10/3);
    (-8), 4;
    0, 8;
    0, (-14);
    (40/3), (-100/3);
    (-8), 4;
    (-28), 22;
    (-8/3), (20/3);
    16, 0;
    6, 0]

theorem f404desc4_step : f407raise*f404desc3=f404desc4 := by
  refine natFourSparseRowProduct_matrix_check f407raise f404desc3 f404desc4
    f407raiseSparseRows f407_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 0) f404desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc4 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 1) f404desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc4 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 2) f404desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc4 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 3) f404desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc4 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 4) f404desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc4 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 5) f404desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc4 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 6) f404desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc4 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 7) f404desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc4 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 8) f404desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc4 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 9) f404desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc4 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 10) f404desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc4 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 11) f404desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc4 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 12) f404desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc4 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 13) f404desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc4 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f407raiseSparseRows 14) f404desc3 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc4 14 b)
      (by decide +kernel) 0 b

theorem f404desc4_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
      (natFourWordBlock f404basis (complexify b404relative *ᵥ x))=
      natFourWordBlock f408basis (complexify f404desc4 *ᵥ x) := by
  exact natFour_descendant_step 3
    (fun x => natFourWordBlock f404basis (complexify b404relative *ᵥ x))
    f407basis f408basis f404desc3 f404desc4 f407raise
    f404desc3_actual f407_actual_raise_block f404desc4_step x

def f404desc5 : Matrix (Fin 18) (Fin 2) ℚ :=
  !![(1/3), (-1/3);
    (11/3), (-11/3);
    (16/3), (-10/3);
    (16/3), (14/3);
    6, 14;
    (20/3), (-26/3);
    0, (-4);
    (-8/3), (68/3);
    (10/3), (50/3);
    (-8), (-10);
    (80/3), (-260/3);
    (40/3), (-100/3);
    (-20/3), (2/3);
    (-60), 38;
    (-100/3), (130/3);
    (-40), 30;
    40, (-20);
    40, 0]

theorem f404desc5_step : f408raise*f404desc4=f404desc5 := by
  refine natFourSparseRowProduct_matrix_check f408raise f404desc4 f404desc5
    f408raiseSparseRows f408_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 0) f404desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc5 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 1) f404desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc5 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 2) f404desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc5 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 3) f404desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc5 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 4) f404desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc5 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 5) f404desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc5 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 6) f404desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc5 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 7) f404desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc5 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 8) f404desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc5 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 9) f404desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc5 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 10) f404desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc5 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 11) f404desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc5 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 12) f404desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc5 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 13) f404desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc5 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 14) f404desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc5 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 15) f404desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc5 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 16) f404desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc5 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f408raiseSparseRows 17) f404desc4 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc5 17 b)
      (by decide +kernel) 0 b

theorem f404desc5_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
      (natFourWordBlock f404basis (complexify b404relative *ᵥ x))=
      natFourWordBlock f409basis (complexify f404desc5 *ᵥ x) := by
  exact natFour_descendant_step 4
    (fun x => natFourWordBlock f404basis (complexify b404relative *ᵥ x))
    f408basis f409basis f404desc4 f404desc5 f408raise
    f404desc4_actual f408_actual_raise_block f404desc5_step x

def f404desc6 : Matrix (Fin 23) (Fin 2) ℚ :=
  !![(1/3), (-1/3);
    (14/3), (-14/3);
    9, (-7);
    (32/3), (4/3);
    (34/3), (56/3);
    6, 14;
    14, (-16);
    24, (-28);
    8, 28;
    16, 84;
    (-8), (-14);
    8, (-84);
    30, (-70);
    (200/3), (-560/3);
    0, (-8);
    (-80), 36;
    (-96), 104;
    (-30), 60;
    (-168), 96;
    (-40), 20;
    (160/3), (-160/3);
    0, 30;
    160, (-20)]

theorem f404desc6_step : f409raise*f404desc5=f404desc6 := by
  refine natFourSparseRowProduct_matrix_check f409raise f404desc5 f404desc6
    f409raiseSparseRows f409_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 0) f404desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc6 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 1) f404desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc6 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 2) f404desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc6 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 3) f404desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc6 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 4) f404desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc6 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 5) f404desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc6 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 6) f404desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc6 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 7) f404desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc6 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 8) f404desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc6 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 9) f404desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc6 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 10) f404desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc6 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 11) f404desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc6 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 12) f404desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc6 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 13) f404desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc6 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 14) f404desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc6 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 15) f404desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc6 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 16) f404desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc6 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 17) f404desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc6 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 18) f404desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc6 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 19) f404desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc6 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 20) f404desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc6 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 21) f404desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc6 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f409raiseSparseRows 22) f404desc5 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc6 22 b)
      (by decide +kernel) 0 b

theorem f404desc6_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6]
      (natFourWordBlock f404basis (complexify b404relative *ᵥ x))=
      natFourWordBlock f410basis (complexify f404desc6 *ᵥ x) := by
  exact natFour_descendant_step 5
    (fun x => natFourWordBlock f404basis (complexify b404relative *ᵥ x))
    f409basis f410basis f404desc5 f404desc6 f409raise
    f404desc5_actual f409_actual_raise_block f404desc6_step x

def f404desc7 : Matrix (Fin 27) (Fin 2) ℚ :=
  !![(1/3), (-1/3);
    (17/3), (-17/3);
    (41/3), (-35/3);
    (59/3), (-17/3);
    22, 20;
    (70/3), (140/3);
    (70/3), (-76/3);
    70, (-74);
    (160/3), (8/3);
    (140/3), (448/3);
    28, 112;
    16, (-42);
    0, (-84);
    84, (-140);
    (224/3), (-812/3);
    (490/3), (-1330/3);
    14, (-24);
    (-56), (-16);
    (-168), 168;
    (-140), 308;
    (-336), 154;
    (-560), 336;
    (-70), 70;
    (560/3), (-980/3);
    (-168), 126;
    280, 70;
    (1120/3), (-280/3)]

theorem f404desc7_step : f410raise*f404desc6=f404desc7 := by
  refine natFourSparseRowProduct_matrix_check f410raise f404desc6 f404desc7
    f410raiseSparseRows f410_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 0) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 1) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 2) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 3) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 4) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 5) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 6) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 7) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 8) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 9) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 10) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 11) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 12) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 13) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 14) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 15) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 16) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 17) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 18) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 19) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 20) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 21) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 22) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 23) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 24) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 25) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f410raiseSparseRows 26) f404desc6 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc7 26 b)
      (by decide +kernel) 0 b

theorem f404desc7_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7]
      (natFourWordBlock f404basis (complexify b404relative *ᵥ x))=
      natFourWordBlock f411basis (complexify f404desc7 *ᵥ x) := by
  exact natFour_descendant_step 6
    (fun x => natFourWordBlock f404basis (complexify b404relative *ᵥ x))
    f410basis f411basis f404desc6 f404desc7 f410raise
    f404desc6_actual f410_actual_raise_block f404desc7_step x

#print axioms f404desc4_step
#print axioms f404desc4_actual
#print axioms f404desc5_step
#print axioms f404desc5_actual
#print axioms f404desc6_step
#print axioms f404desc6_actual
#print axioms f404desc7_step
#print axioms f404desc7_actual
end TorusLean.BosonFiniteCertificate
