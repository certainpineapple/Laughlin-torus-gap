import torus.shared.BosonFiniteCertificateNatFourRaiseSparse415
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates404P15

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

def f404desc12 : Matrix (Fin 64) (Fin 2) ℚ :=
  !![(1/3), (-1/3);
    (32/3), (-32/3);
    52, (-50);
    (464/3), (-392/3);
    (956/3), (-560/3);
    496, (-56);
    (1892/3), (1078/3);
    704, 880;
    363, 561;
    100, (-102);
    840, (-844);
    (6320/3), (-5672/3);
    3600, (-2104);
    4664, 396;
    (15400/3), (16676/3);
    5280, 10032;
    1476, (-1522);
    6000, (-5864);
    8184, (-5500);
    8888, 1100;
    9240, 10692;
    4752, 7656;
    (14344/3), (-15532/3);
    (32560/3), (-36520/3);
    12672, (-11616);
    15840, (-11088);
    7260, (-14520);
    24288, (-55440);
    15400, (-34804);
    20328, (-52668);
    264, (-284);
    2684, (-2986);
    5072, (-5272);
    5940, (-3102);
    4840, 6996;
    3564, 20526;
    1584, 13464;
    6624, (-8496);
    14080, (-21824);
    1320, (-220);
    (-11880), 46332;
    (-14784), 85536;
    (-9680/3), (-25960/3);
    (-34320), 3960;
    (-31680), 17952;
    (-9856), 9856;
    (-15840), (-23760);
    18480, (-131208);
    11088, (-38808);
    2112, (-5544);
    (-15840), (-6160);
    (-45540), 30690;
    (-50688), 69696;
    (-22176), 42504;
    (-69960), 25740;
    (-163680), 97680;
    (-73920), 81312;
    (-9240), (-13860);
    60984, (-69300);
    (-38720), 22880;
    (-6160), 33880;
    48048, (-5544);
    221760, (-73920);
    34650, (-11550)]

theorem f404desc12_step : f415raise*f404desc11=f404desc12 := by
  refine natFourSparseRowProduct_matrix_check f415raise f404desc11 f404desc12
    f415raiseSparseRows f415_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 0) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 1) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 2) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 3) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 4) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 5) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 6) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 7) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 8) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 9) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 10) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 11) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 12) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 13) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 14) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 15) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 16) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 17) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 18) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 19) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 20) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 21) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 22) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 23) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 24) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 25) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 26) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 27) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 28) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 29) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 30) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 31) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 32) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 33) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 34) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 35) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 36) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 37) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 38) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 39) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 40) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 41) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 42) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 43) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 44) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 45) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 46) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 47) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 48) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 49) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 50) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 51) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 52) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 53) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 53 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 54) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 54 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 55) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 55 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 56) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 56 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 57) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 57 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 58) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 58 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 59) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 59 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 60) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 60 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 61) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 61 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 62) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 62 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 2) => natFourSparseRowProduct (f415raiseSparseRows 63) f404desc11 b)
      (fun (_ : Fin 1) (b : Fin 2) => f404desc12 63 b)
      (by decide +kernel) 0 b

theorem f404desc12_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[12]
      (natFourWordBlock f404basis (complexify b404relative *ᵥ x))=
      natFourWordBlock f416basis (complexify f404desc12 *ᵥ x) := by
  exact natFour_descendant_step 11
    (fun x => natFourWordBlock f404basis (complexify b404relative *ᵥ x))
    f415basis f416basis f404desc11 f404desc12 f415raise
    f404desc11_actual f415_actual_raise_block f404desc12_step x

#print axioms f404desc12_step
#print axioms f404desc12_actual
end TorusLean.BosonFiniteCertificate
