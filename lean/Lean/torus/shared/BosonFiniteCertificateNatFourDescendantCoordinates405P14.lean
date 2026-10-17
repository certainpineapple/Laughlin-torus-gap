import torus.shared.BosonFiniteCertificateNatFourRaiseSparse413
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates405P13

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

def f405desc9 : Matrix (Fin 47) (Fin 1) ℚ :=
  !![(-1/6);
    (-11/3);
    (-65/6);
    (-46/3);
    (-43/6);
    9;
    (37/2);
    10;
    (-67/3);
    (-100);
    (-236/3);
    (134/3);
    114;
    72;
    (-59);
    (388/3);
    411;
    312;
    70;
    334;
    856;
    504;
    399;
    294;
    (-36);
    (-162);
    (-52/3);
    81;
    (-216);
    (-238);
    (-26);
    684;
    (-72);
    (-2184);
    432;
    (-1288);
    (-1512);
    (-1386);
    171;
    648;
    (-966);
    (-1134);
    392;
    (-504);
    315;
    1008;
    2730]

theorem f405desc9_step : f413raise*f405desc8=f405desc9 := by
  refine natFourSparseRowProduct_matrix_check f413raise f405desc8 f405desc9
    f413raiseSparseRows f413_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 0) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 1) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 2) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 3) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 4) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 5) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 6) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 7) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 8) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 9) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 10) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 11) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 12) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 13) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 14) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 15) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 16) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 17) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 18) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 19) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 20) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 21) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 22) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 23) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 24) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 25) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 26) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 27) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 28) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 29) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 30) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 31) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 32) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 33) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 34) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 35) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 36) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 37) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 38) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 39) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 40) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 41) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 42) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 43) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 44) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 45) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 46) f405desc8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc9 46 b)
      (by decide +kernel) 0 b

theorem f405desc9_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[9]
      (natFourWordBlock f405basis (complexify b405relative *ᵥ x))=
      natFourWordBlock f414basis (complexify f405desc9 *ᵥ x) := by
  exact natFour_descendant_step 8
    (fun x => natFourWordBlock f405basis (complexify b405relative *ᵥ x))
    f413basis f414basis f405desc8 f405desc9 f413raise
    f405desc8_actual f413_actual_raise_block f405desc9_step x

#print axioms f405desc9_step
#print axioms f405desc9_actual
end TorusLean.BosonFiniteCertificate
