import torus.shared.BosonFiniteCertificateNatFourRaiseSparse413
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates403P13

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

def f403desc11 : Matrix (Fin 47) (Fin 1) ℚ :=
  !![(1/2);
    15;
    (129/2);
    150;
    (363/2);
    33;
    (-495/2);
    (-198);
    135;
    1020;
    1980;
    1650;
    (-990);
    (-3960);
    1617;
    4620;
    495;
    (-8712);
    (-6930);
    990;
    (-11880);
    (-27720);
    (-17325);
    (-23562);
    364;
    3630;
    5940;
    3465;
    (-3960);
    (-4158);
    10230;
    25740;
    3960;
    (-27720);
    7920;
    (-27720);
    (-27720);
    (-34650);
    8415;
    27720;
    6930;
    (-4158);
    27720;
    27720;
    5775;
    18480;
    34650]

theorem f403desc11_step : f413raise*f403desc10=f403desc11 := by
  refine natFourSparseRowProduct_matrix_check f413raise f403desc10 f403desc11
    f413raiseSparseRows f413_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 0) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 1) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 2) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 3) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 4) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 5) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 6) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 7) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 8) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 9) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 10) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 11) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 12) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 13) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 14) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 15) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 16) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 17) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 18) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 19) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 20) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 21) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 22) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 23) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 24) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 25) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 26) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 27) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 28) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 29) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 30) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 31) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 32) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 33) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 34) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 35) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 36) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 37) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 38) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 39) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 40) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 41) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 42) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 43) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 44) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 45) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f413raiseSparseRows 46) f403desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc11 46 b)
      (by decide +kernel) 0 b

theorem f403desc11_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[11]
      (natFourWordBlock f403basis (complexify b403relative *ᵥ x))=
      natFourWordBlock f414basis (complexify f403desc11 *ᵥ x) := by
  exact natFour_descendant_step 10
    (fun x => natFourWordBlock f403basis (complexify b403relative *ᵥ x))
    f413basis f414basis f403desc10 f403desc11 f413raise
    f403desc10_actual f413_actual_raise_block f403desc11_step x

#print axioms f403desc11_step
#print axioms f403desc11_actual
end TorusLean.BosonFiniteCertificate
