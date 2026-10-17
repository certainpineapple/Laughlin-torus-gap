import torus.shared.BosonFiniteCertificateNatFourRaiseSparse413
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates404P13

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

def f404desc10 : Matrix (Fin 47) (Fin 2) ℚ :=
  !![(1/3), (-1/3);
    (26/3), (-26/3);
    (101/3), (-95/3);
    (236/3), (-176/3);
    (383/3), (-113/3);
    162, 78;
    179, 241;
    92, 160;
    (190/3), (-196/3);
    400, (-404);
    (2192/3), (-1772/3);
    (2740/3), (-400/3);
    948, 1092;
    960, 2232;
    482, (-520);
    (3760/3), (-3820/3);
    1170, (-390);
    1248, 1080;
    700, 896;
    580, (-1000);
    1520, (-3440);
    2688, (-5208);
    1890, (-5250);
    2772, (-7392);
    120, (-136);
    780, (-972);
    (2200/3), (-2440/3);
    150, 1020;
    (-240), 3696;
    (-140), 2492;
    620, (-1540);
    (-2640), (-180);
    (-5760), 6120;
    (-5040), 10752;
    (-4320), 960;
    (-5600), (-1960);
    (-336), (-3024);
    2940, (-10500);
    (-1170), 0;
    (-9360), 4800;
    (-7980), 7560;
    (-2268), 3780;
    (-9520), 6160;
    6720, (-840);
    5250, (-3150);
    3360, 0;
    14700, (-4200)]

theorem f404desc10_step : f413raise*f404desc9=f404desc10 := by
  refine natFourSparseRowProduct_matrix_check f413raise f404desc9 f404desc10
    f413raiseSparseRows f413_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 0) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 1) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 2) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 3) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 4) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 5) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 6) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 7) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 8) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 9) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 10) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 11) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 12) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 13) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 14) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 15) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 16) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 17) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 18) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 19) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 20) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 21) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 22) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 23) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 24) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 25) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 26) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 27) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 28) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 29) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 30) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 31) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 32) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 33) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 34) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 35) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 36) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 37) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 38) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 39) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 40) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 41) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 42) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 43) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 44) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 45) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f413raiseSparseRows 46) f404desc9 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc10 46 b)
      (by decide +kernel) 0 b

theorem f404desc10_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[10]
      (natFourWordBlock f404basis (complexify b404relative *ᵥ x))=
      natFourWordBlock f414basis (complexify f404desc10 *ᵥ x) := by
  exact natFour_descendant_step 9
    (fun x => natFourWordBlock f404basis (complexify b404relative *ᵥ x))
    f413basis f414basis f404desc9 f404desc10 f413raise
    f404desc9_actual f413_actual_raise_block f404desc10_step x

#print axioms f404desc10_step
#print axioms f404desc10_actual
end TorusLean.BosonFiniteCertificate
