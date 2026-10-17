import torus.shared.BosonFiniteCertificateNatFourRaiseSparse407
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse408
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse409
import torus.shared.BosonFiniteCertificateNatFourRaiseSparse410
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates403P07

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

def f403desc5 : Matrix (Fin 15) (Fin 1) ℚ :=
  !![(1/2);
    6;
    6;
    (-6);
    (-15/2);
    18;
    12;
    (-60);
    (-30);
    (-60);
    16;
    30;
    0;
    60;
    15]

theorem f403desc5_step : f407raise*f403desc4=f403desc5 := by
  refine natFourSparseRowProduct_matrix_check f407raise f403desc4 f403desc5
    f407raiseSparseRows f407_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 0) f403desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc5 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 1) f403desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc5 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 2) f403desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc5 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 3) f403desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc5 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 4) f403desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc5 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 5) f403desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc5 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 6) f403desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc5 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 7) f403desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc5 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 8) f403desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc5 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 9) f403desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc5 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 10) f403desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc5 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 11) f403desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc5 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 12) f403desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc5 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 13) f403desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc5 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f407raiseSparseRows 14) f403desc4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc5 14 b)
      (by decide +kernel) 0 b

theorem f403desc5_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
      (natFourWordBlock f403basis (complexify b403relative *ᵥ x))=
      natFourWordBlock f408basis (complexify f403desc5 *ᵥ x) := by
  exact natFour_descendant_step 4
    (fun x => natFourWordBlock f403basis (complexify b403relative *ᵥ x))
    f407basis f408basis f403desc4 f403desc5 f407raise
    f403desc4_actual f407_actual_raise_block f403desc5_step x

def f403desc6 : Matrix (Fin 18) (Fin 1) ℚ :=
  !![(1/2);
    (15/2);
    12;
    0;
    (-21);
    30;
    60;
    (-60);
    (-75);
    (-18);
    (-240);
    (-60);
    34;
    90;
    (-30);
    90;
    60;
    120]

theorem f403desc6_step : f408raise*f403desc5=f403desc6 := by
  refine natFourSparseRowProduct_matrix_check f408raise f403desc5 f403desc6
    f408raiseSparseRows f408_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 0) f403desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc6 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 1) f403desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc6 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 2) f403desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc6 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 3) f403desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc6 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 4) f403desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc6 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 5) f403desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc6 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 6) f403desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc6 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 7) f403desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc6 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 8) f403desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc6 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 9) f403desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc6 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 10) f403desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc6 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 11) f403desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc6 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 12) f403desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc6 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 13) f403desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc6 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 14) f403desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc6 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 15) f403desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc6 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 16) f403desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc6 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f408raiseSparseRows 17) f403desc5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc6 17 b)
      (by decide +kernel) 0 b

theorem f403desc6_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6]
      (natFourWordBlock f403basis (complexify b403relative *ᵥ x))=
      natFourWordBlock f409basis (complexify f403desc6 *ᵥ x) := by
  exact natFour_descendant_step 5
    (fun x => natFourWordBlock f403basis (complexify b403relative *ᵥ x))
    f408basis f409basis f403desc5 f403desc6 f408raise
    f403desc5_actual f408_actual_raise_block f403desc6_step x

def f403desc7 : Matrix (Fin 23) (Fin 1) ℚ :=
  !![(1/2);
    9;
    (39/2);
    12;
    (-21);
    (-21);
    45;
    144;
    0;
    (-252);
    42;
    (-336);
    (-315);
    (-420);
    64;
    252;
    0;
    (-105);
    252;
    0;
    0;
    210;
    420]

theorem f403desc7_step : f409raise*f403desc6=f403desc7 := by
  refine natFourSparseRowProduct_matrix_check f409raise f403desc6 f403desc7
    f409raiseSparseRows f409_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 0) f403desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc7 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 1) f403desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc7 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 2) f403desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc7 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 3) f403desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc7 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 4) f403desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc7 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 5) f403desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc7 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 6) f403desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc7 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 7) f403desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc7 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 8) f403desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc7 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 9) f403desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc7 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 10) f403desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc7 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 11) f403desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc7 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 12) f403desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc7 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 13) f403desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc7 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 14) f403desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc7 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 15) f403desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc7 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 16) f403desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc7 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 17) f403desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc7 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 18) f403desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc7 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 19) f403desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc7 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 20) f403desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc7 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 21) f403desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc7 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f409raiseSparseRows 22) f403desc6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc7 22 b)
      (by decide +kernel) 0 b

theorem f403desc7_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7]
      (natFourWordBlock f403basis (complexify b403relative *ᵥ x))=
      natFourWordBlock f410basis (complexify f403desc7 *ᵥ x) := by
  exact natFour_descendant_step 6
    (fun x => natFourWordBlock f403basis (complexify b403relative *ᵥ x))
    f409basis f410basis f403desc6 f403desc7 f409raise
    f403desc6_actual f409_actual_raise_block f403desc7_step x

def f403desc8 : Matrix (Fin 27) (Fin 1) ℚ :=
  !![(1/2);
    (21/2);
    (57/2);
    (63/2);
    (-9);
    (-63);
    63;
    273;
    168;
    (-294);
    (-294);
    186;
    (-252);
    (-1218);
    (-756);
    (-1155);
    109;
    588;
    252;
    (-462);
    798;
    168;
    (-525);
    (-420);
    462;
    1470;
    840]

theorem f403desc8_step : f410raise*f403desc7=f403desc8 := by
  refine natFourSparseRowProduct_matrix_check f410raise f403desc7 f403desc8
    f410raiseSparseRows f410_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 0) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 1) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 2) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 3) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 4) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 5) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 6) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 7) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 8) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 9) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 10) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 11) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 12) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 13) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 14) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 15) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 16) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 17) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 18) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 19) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 20) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 21) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 22) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 23) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 24) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 25) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f410raiseSparseRows 26) f403desc7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc8 26 b)
      (by decide +kernel) 0 b

theorem f403desc8_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8]
      (natFourWordBlock f403basis (complexify b403relative *ᵥ x))=
      natFourWordBlock f411basis (complexify f403desc8 *ᵥ x) := by
  exact natFour_descendant_step 7
    (fun x => natFourWordBlock f403basis (complexify b403relative *ᵥ x))
    f410basis f411basis f403desc7 f403desc8 f410raise
    f403desc7_actual f410_actual_raise_block f403desc8_step x

#print axioms f403desc5_step
#print axioms f403desc5_actual
#print axioms f403desc6_step
#print axioms f403desc6_actual
#print axioms f403desc7_step
#print axioms f403desc7_actual
#print axioms f403desc8_step
#print axioms f403desc8_actual
end TorusLean.BosonFiniteCertificate
