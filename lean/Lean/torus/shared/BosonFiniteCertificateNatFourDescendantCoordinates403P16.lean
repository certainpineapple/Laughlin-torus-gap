import torus.shared.BosonFiniteCertificateNatFourRaiseSparse415
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates403P15

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

def f403desc13 : Matrix (Fin 64) (Fin 1) ℚ :=
  !![(1/2);
    18;
    96;
    294;
    546;
    546;
    0;
    (-858);
    (-1287/2);
    198;
    1908;
    5148;
    7956;
    5148;
    (-5148);
    (-15444);
    4056;
    18408;
    20592;
    (-1716);
    (-41184);
    (-30888);
    15444;
    8580;
    (-66924);
    (-144144);
    (-38610);
    (-216216);
    (-144144);
    (-180180);
    664;
    8658;
    20592;
    26598;
    10296;
    (-23166);
    (-20592);
    33228;
    133848;
    128700;
    (-15444);
    (-185328);
    102960;
    77220;
    (-247104);
    (-216216);
    (-128700);
    (-648648);
    (-144144);
    37752;
    197340;
    154440;
    (-30888);
    (-72072);
    283140;
    308880;
    (-144144);
    0;
    (-108108);
    137280;
    360360;
    144144;
    540540;
    75075]

theorem f403desc13_step : f415raise*f403desc12=f403desc13 := by
  refine natFourSparseRowProduct_matrix_check f415raise f403desc12 f403desc13
    f415raiseSparseRows f415_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 0) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 1) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 2) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 3) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 4) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 5) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 6) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 7) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 8) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 9) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 10) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 11) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 12) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 13) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 14) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 15) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 16) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 17) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 18) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 19) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 20) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 21) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 22) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 23) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 24) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 25) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 26) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 27) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 28) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 29) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 30) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 31) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 32) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 33) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 34) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 35) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 36) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 37) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 38) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 39) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 40) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 41) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 42) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 43) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 44) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 45) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 46) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 47) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 48) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 49) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 50) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 51) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 52) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 53) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 53 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 54) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 54 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 55) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 55 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 56) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 56 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 57) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 57 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 58) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 58 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 59) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 59 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 60) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 60 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 61) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 61 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 62) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 62 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 63) f403desc12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc13 63 b)
      (by decide +kernel) 0 b

theorem f403desc13_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[13]
      (natFourWordBlock f403basis (complexify b403relative *ᵥ x))=
      natFourWordBlock f416basis (complexify f403desc13 *ᵥ x) := by
  exact natFour_descendant_step 12
    (fun x => natFourWordBlock f403basis (complexify b403relative *ᵥ x))
    f415basis f416basis f403desc12 f403desc13 f415raise
    f403desc12_actual f415_actual_raise_block f403desc13_step x

#print axioms f403desc13_step
#print axioms f403desc13_actual
end TorusLean.BosonFiniteCertificate
