import torus.shared.BosonFiniteCertificateNatFourRaiseSparse414
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates405P14

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

def f405desc10 : Matrix (Fin 54) (Fin 1) ℚ :=
  !![(-1/6);
    (-25/6);
    (-29/2);
    (-157/6);
    (-45/2);
    (11/6);
    (55/2);
    (77/2);
    (-89/3);
    (-499/3);
    (-628/3);
    (-145/3);
    (530/3);
    223;
    92;
    (-159);
    (-202/3);
    585;
    837;
    524;
    (1390/3);
    1935;
    1672;
    574;
    1255;
    1890;
    294;
    (-175/3);
    (-370);
    (-258);
    (325/3);
    (-21);
    (-620);
    (-409);
    (2180/3);
    1185;
    (-2376);
    (-2590);
    1450;
    360;
    (-5992);
    (-2275);
    (-3990);
    145;
    1845;
    (-390);
    (-5418);
    2120;
    (-2940);
    (-4284);
    (-945);
    1400;
    7980;
    5775]

theorem f405desc10_step : f414raise*f405desc9=f405desc10 := by
  refine natFourSparseRowProduct_matrix_check f414raise f405desc9 f405desc10
    f414raiseSparseRows f414_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 0) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 1) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 2) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 3) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 4) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 5) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 6) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 7) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 8) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 9) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 10) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 11) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 12) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 13) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 14) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 15) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 16) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 17) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 18) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 19) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 20) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 21) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 22) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 23) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 24) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 25) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 26) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 27) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 28) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 29) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 30) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 31) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 32) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 33) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 34) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 35) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 36) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 37) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 38) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 39) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 40) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 41) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 42) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 43) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 44) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 45) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 46) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 47) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 48) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 49) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 50) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 51) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 52) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 53) f405desc9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc10 53 b)
      (by decide +kernel) 0 b

theorem f405desc10_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[10]
      (natFourWordBlock f405basis (complexify b405relative *ᵥ x))=
      natFourWordBlock f415basis (complexify f405desc10 *ᵥ x) := by
  exact natFour_descendant_step 9
    (fun x => natFourWordBlock f405basis (complexify b405relative *ᵥ x))
    f414basis f415basis f405desc9 f405desc10 f414raise
    f405desc9_actual f414_actual_raise_block f405desc10_step x

#print axioms f405desc10_step
#print axioms f405desc10_actual
end TorusLean.BosonFiniteCertificate
