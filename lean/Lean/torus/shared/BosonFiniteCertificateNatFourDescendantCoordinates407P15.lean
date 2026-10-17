import torus.shared.BosonFiniteCertificateNatFourRaiseSparse414
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates407P14

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

def f407desc8 : Matrix (Fin 54) (Fin 2) ℚ :=
  !![(1/20), (-1/15);
    (17/20), (-17/15);
    (37/20), (-32/15);
    (39/20), (-4/15);
    (5/4), (14/3);
    (11/20), (94/15);
    (-33/20), (1/5);
    (-99/20), (-37/5);
    (17/5), (-73/15);
    (69/10), (-148/15);
    (-14/5), (72/5);
    (-21/10), (184/5);
    (38/5), (86/5);
    (-13/2), (-74/3);
    (-58/5), (-328/15);
    (-39/5), (71/15);
    (-214/5), (526/15);
    (-41/2), (20/3);
    (-141/10), (-96/5);
    (-356/5), (244/15);
    (-27), (-44/3);
    (-35/2), (-304/3);
    (-292/5), (608/15);
    (-294/5), (462/5);
    (-1/2), (-14/3);
    (-63/5), (1484/5);
    (42/5), (1162/15);
    2, (-13/3);
    (-12), (14/3);
    (-88/5), (542/15);
    44, (35/3);
    (429/5), (-177/5);
    44, (-100/3);
    (-273/5), (617/15);
    0, (-12);
    (519/2), (-644/3);
    (696/5), (-344/15);
    (-42), (350/3);
    121, (-628/3);
    308, (-1648/3);
    0, (-392/3);
    (357/2), (-406);
    (1092/5), (-6958/15);
    (-21), (47/3);
    63, (-109/3);
    (-12), 134;
    (-1932/5), (8918/15);
    (-76), 144;
    (-672), (2212/3);
    (-2184/5), (6356/15);
    (105/2), (-1036/3);
    (-140), 224;
    210, (-112/3);
    (945/2), (-420)]

theorem f407desc8_step : f414raise*f407desc7=f407desc8 := by
  refine natFourSparseRowProduct_matrix_check f414raise f407desc7 f407desc8
    f414raiseSparseRows f414_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 0) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 1) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 2) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 3) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 4) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 5) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 6) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 7) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 8) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 9) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 10) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 11) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 12) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 13) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 14) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 15) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 16) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 17) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 18) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 19) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 20) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 21) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 22) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 23) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 24) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 25) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 26) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 27) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 28) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 29) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 30) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 31) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 32) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 33) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 34) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 35) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 36) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 37) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 38) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 39) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 40) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 41) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 42) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 43) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 44) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 45) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 46) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 47) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 48) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 49) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 50) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 51) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 52) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 53) f407desc7 b)
      (fun (_ : Fin 1) (b : Fin 2) => f407desc8 53 b)
      (by decide +kernel) 0 b

theorem f407desc8_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8]
      (natFourWordBlock f407basis (complexify b407relative *ᵥ x))=
      natFourWordBlock f415basis (complexify f407desc8 *ᵥ x) := by
  exact natFour_descendant_step 7
    (fun x => natFourWordBlock f407basis (complexify b407relative *ᵥ x))
    f414basis f415basis f407desc7 f407desc8 f414raise
    f407desc7_actual f414_actual_raise_block f407desc8_step x

#print axioms f407desc8_step
#print axioms f407desc8_actual
end TorusLean.BosonFiniteCertificate
