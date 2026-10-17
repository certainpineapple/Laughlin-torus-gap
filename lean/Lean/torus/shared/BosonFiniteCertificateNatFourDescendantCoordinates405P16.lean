import torus.shared.BosonFiniteCertificateNatFourRaiseSparse415
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates405P15

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

def f405desc11 : Matrix (Fin 64) (Fin 1) ℚ :=
  !![(-1/6);
    (-14/3);
    (-56/3);
    (-122/3);
    (-146/3);
    (-62/3);
    (88/3);
    66;
    (77/2);
    (-38);
    (-764/3);
    (-428);
    (-908/3);
    132;
    (1364/3);
    484;
    (-976/3);
    (-1784/3);
    (1408/3);
    (4796/3);
    1584;
    616;
    396;
    (10340/3);
    4444;
    3344;
    3190;
    6072;
    2464;
    2772;
    (-88);
    (-2134/3);
    (-2512/3);
    (-198);
    264;
    (-418);
    (-528);
    (-1308);
    (-2024/3);
    (8140/3);
    (-396);
    (-8272);
    2640;
    6380;
    (-6336);
    (-8008);
    (-660);
    (-16632);
    (-3696);
    (-264);
    (9020/3);
    2640;
    (-8184);
    (-8008);
    7260;
    880;
    (-28336);
    (-6160);
    (-10164);
    3520;
    9240;
    3696;
    32340;
    5775]

theorem f405desc11_step : f415raise*f405desc10=f405desc11 := by
  refine natFourSparseRowProduct_matrix_check f415raise f405desc10 f405desc11
    f415raiseSparseRows f415_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 0) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 1) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 2) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 3) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 4) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 5) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 6) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 7) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 8) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 9) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 10) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 11) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 12) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 13) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 14) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 15) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 16) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 17) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 18) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 19) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 20) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 21) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 22) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 23) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 24) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 25) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 26) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 27) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 28) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 29) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 30) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 31) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 32) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 33) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 34) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 35) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 36) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 37) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 38) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 39) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 40) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 41) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 42) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 43) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 44) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 45) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 46) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 47) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 48) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 49) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 50) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 51) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 52) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 53) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 53 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 54) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 54 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 55) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 55 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 56) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 56 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 57) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 57 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 58) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 58 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 59) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 59 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 60) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 60 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 61) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 61 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 62) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 62 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f415raiseSparseRows 63) f405desc10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f405desc11 63 b)
      (by decide +kernel) 0 b

theorem f405desc11_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[11]
      (natFourWordBlock f405basis (complexify b405relative *ᵥ x))=
      natFourWordBlock f416basis (complexify f405desc11 *ᵥ x) := by
  exact natFour_descendant_step 10
    (fun x => natFourWordBlock f405basis (complexify b405relative *ᵥ x))
    f415basis f416basis f405desc10 f405desc11 f415raise
    f405desc10_actual f415_actual_raise_block f405desc11_step x

#print axioms f405desc11_step
#print axioms f405desc11_actual
end TorusLean.BosonFiniteCertificate
