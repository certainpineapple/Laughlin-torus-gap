import torus.shared.BosonFiniteCertificateNatFourRaiseSparse414
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates404P14

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

def f404desc11 : Matrix (Fin 54) (Fin 2) ℚ :=
  !![(1/3), (-1/3);
    (29/3), (-29/3);
    (127/3), (-121/3);
    (337/3), (-271/3);
    (619/3), (-289/3);
    (869/3), (121/3);
    341, 319;
    363, 561;
    (242/3), (-248/3);
    594, (-598);
    1288, (-1112);
    (5698/3), (-2398/3);
    (6556/3), (3344/3);
    2266, 3806;
    1144, 2552;
    882, (-924);
    2948, (-2904);
    (10010/3), (-5390/3);
    3366, 1782;
    3608, 5104;
    (5500/3), (-6820/3);
    3850, (-5830);
    5456, (-7568);
    3388, (-4312);
    3410, (-8690);
    12012, (-30492);
    2772, (-7392);
    (550/3), (-604/3);
    1540, (-1784);
    2244, (-2376);
    (5390/3), (220/3);
    858, 5808;
    440, 10912;
    2662, (-4004);
    1320, (-6160);
    (-6930), 7590;
    (-10032), 25344;
    (-4620), 16632;
    (-6380), (-220);
    (-18480), 2640;
    (-8624), (-2464);
    (-770), (-17710);
    8316, (-31416);
    (-550), (-1540);
    (-15510), 4620;
    (-23100), 18480;
    (-17556), 25872;
    (-32560), 16720;
    (-33880), 24640;
    1848, 3696;
    25410, (-20790);
    (-6160), 6160;
    46200, (-9240);
    34650, (-11550)]

theorem f404desc11_step : f414raise*f404desc10=f404desc11 := by
  refine natFourSparseRowProduct_matrix_check f414raise f404desc10 f404desc11
    f414raiseSparseRows f414_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 0) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 1) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 2) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 3) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 4) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 5) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 6) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 7) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 8) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 9) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 10) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 11) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 12) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 13) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 14) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 15) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 16) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 17) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 18) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 19) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 20) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 21) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 22) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 23) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 24) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 25) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 26) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 27) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 28) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 29) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 30) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 31) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 32) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 33) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 34) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 35) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 36) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 37) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 38) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 39) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 40) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 41) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 42) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 43) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 44) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 45) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 46) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 47) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 48) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 49) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 50) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 51) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 52) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f414raiseSparseRows 53) f404desc10 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc11 53 b)
      (by decide +kernel) 0 b

theorem f404desc11_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[11]
      (natFourWordBlock f404basis (complexify b404relative *ᵥ x))=
      natFourWordBlock f415basis (complexify f404desc11 *ᵥ x) := by
  exact natFour_descendant_step 10
    (fun x => natFourWordBlock f404basis (complexify b404relative *ᵥ x))
    f414basis f415basis f404desc10 f404desc11 f414raise
    f404desc10_actual f414_actual_raise_block f404desc11_step x

#print axioms f404desc11_step
#print axioms f404desc11_actual
end TorusLean.BosonFiniteCertificate
