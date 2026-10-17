import torus.shared.BosonFiniteCertificateNatFourRaiseSparse407
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse408
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse409
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse410
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates405P07

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

def f405desc3 : Matrix (Fin 15) (Fin 1) ℚ :=
  !![(-1/6);
    (-2/3);
    (2/3);
    (2/3);
    (-1/6);
    (2/3);
    4;
    (-4);
    2;
    (4/3);
    0;
    (-6);
    (-16/3);
    4;
    3]

theorem f405desc3_step : f407raise*f405desc2=f405desc3 := by
  refine natFourSparseRowProduct_matrix_check f407raise f405desc2 f405desc3
    f407raiseSparseRows f407_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 0) f405desc2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc3 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 1) f405desc2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc3 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 2) f405desc2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc3 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 3) f405desc2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc3 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 4) f405desc2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc3 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 5) f405desc2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc3 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 6) f405desc2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc3 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 7) f405desc2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc3 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 8) f405desc2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc3 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 9) f405desc2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc3 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 10) f405desc2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc3 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 11) f405desc2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc3 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 12) f405desc2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc3 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 13) f405desc2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc3 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 14) f405desc2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc3 14 b)
      (by decide +kernel) 0 b

theorem f405desc3_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
      (natFourWordBlock f405basis (complexify b405relative *ᵥ x))=
      natFourWordBlock f408basis (complexify f405desc3 *ᵥ x) := by
  exact natFour_descendant_step 2
    (fun x => natFourWordBlock f405basis (complexify b405relative *ᵥ x))
    f407basis f408basis f405desc2 f405desc3 f407raise
    f405desc2_actual f407_actual_raise_block f405desc3_step x

def f405desc4 : Matrix (Fin 18) (Fin 1) ℚ :=
  !![(-1/6);
    (-7/6);
    0;
    (4/3);
    (1/3);
    (-2/3);
    (20/3);
    (4/3);
    (-13/3);
    6;
    (8/3);
    (4/3);
    (2/3);
    (-2);
    (-62/3);
    (-6);
    (-4/3);
    16]

theorem f405desc4_step : f408raise*f405desc3=f405desc4 := by
  refine natFourSparseRowProduct_matrix_check f408raise f405desc3 f405desc4
    f408raiseSparseRows f408_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 0) f405desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc4 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 1) f405desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc4 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 2) f405desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc4 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 3) f405desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc4 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 4) f405desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc4 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 5) f405desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc4 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 6) f405desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc4 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 7) f405desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc4 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 8) f405desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc4 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 9) f405desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc4 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 10) f405desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc4 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 11) f405desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc4 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 12) f405desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc4 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 13) f405desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc4 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 14) f405desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc4 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 15) f405desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc4 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 16) f405desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc4 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 17) f405desc3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc4 17 b)
      (by decide +kernel) 0 b

theorem f405desc4_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
      (natFourWordBlock f405basis (complexify b405relative *ᵥ x))=
      natFourWordBlock f409basis (complexify f405desc4 *ᵥ x) := by
  exact natFour_descendant_step 3
    (fun x => natFourWordBlock f405basis (complexify b405relative *ᵥ x))
    f408basis f409basis f405desc3 f405desc4 f408raise
    f405desc3_actual f408_actual_raise_block f405desc4_step x

def f405desc5 : Matrix (Fin 23) (Fin 1) ℚ :=
  !![(-1/6);
    (-5/3);
    (-7/6);
    (4/3);
    (5/3);
    (1/3);
    (-3);
    (16/3);
    (32/3);
    (-20/3);
    (38/3);
    16;
    (-5/3);
    (20/3);
    0;
    (20/3);
    (-64/3);
    (-25);
    (-4);
    (-160/3);
    0;
    10;
    (140/3)]

theorem f405desc5_step : f409raise*f405desc4=f405desc5 := by
  refine natFourSparseRowProduct_matrix_check f409raise f405desc4 f405desc5
    f409raiseSparseRows f409_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 0) f405desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc5 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 1) f405desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc5 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 2) f405desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc5 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 3) f405desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc5 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 4) f405desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc5 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 5) f405desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc5 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 6) f405desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc5 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 7) f405desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc5 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 8) f405desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc5 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 9) f405desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc5 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 10) f405desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc5 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 11) f405desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc5 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 12) f405desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc5 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 13) f405desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc5 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 14) f405desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc5 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 15) f405desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc5 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 16) f405desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc5 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 17) f405desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc5 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 18) f405desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc5 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 19) f405desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc5 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 20) f405desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc5 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 21) f405desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc5 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 22) f405desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc5 22 b)
      (by decide +kernel) 0 b

theorem f405desc5_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
      (natFourWordBlock f405basis (complexify b405relative *ᵥ x))=
      natFourWordBlock f410basis (complexify f405desc5 *ᵥ x) := by
  exact natFour_descendant_step 4
    (fun x => natFourWordBlock f405basis (complexify b405relative *ᵥ x))
    f409basis f410basis f405desc4 f405desc5 f409raise
    f405desc4_actual f409_actual_raise_block f405desc5_step x

def f405desc6 : Matrix (Fin 27) (Fin 1) ℚ :=
  !![(-1/6);
    (-13/6);
    (-17/6);
    (1/6);
    3;
    (7/3);
    (-19/3);
    (-3);
    (56/3);
    (22/3);
    (-6);
    18;
    52;
    6;
    (68/3);
    (35/3);
    (-3);
    12;
    (-4);
    (-78);
    22;
    (-88);
    (-105);
    (-140/3);
    6;
    70;
    (280/3)]

theorem f405desc6_step : f410raise*f405desc5=f405desc6 := by
  refine natFourSparseRowProduct_matrix_check f410raise f405desc5 f405desc6
    f410raiseSparseRows f410_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 0) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 1) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 2) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 3) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 4) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 5) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 6) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 7) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 8) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 9) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 10) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 11) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 12) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 13) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 14) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 15) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 16) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 17) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 18) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 19) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 20) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 21) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 22) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 23) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 24) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 25) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 26) f405desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc6 26 b)
      (by decide +kernel) 0 b

theorem f405desc6_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6]
      (natFourWordBlock f405basis (complexify b405relative *ᵥ x))=
      natFourWordBlock f411basis (complexify f405desc6 *ᵥ x) := by
  exact natFour_descendant_step 5
    (fun x => natFourWordBlock f405basis (complexify b405relative *ᵥ x))
    f410basis f411basis f405desc5 f405desc6 f410raise
    f405desc5_actual f410_actual_raise_block f405desc6_step x

#print axioms f405desc3_step
#print axioms f405desc3_actual
#print axioms f405desc4_step
#print axioms f405desc4_actual
#print axioms f405desc5_step
#print axioms f405desc5_actual
#print axioms f405desc6_step
#print axioms f405desc6_actual
end TorusLean.BosonFiniteCertificate
