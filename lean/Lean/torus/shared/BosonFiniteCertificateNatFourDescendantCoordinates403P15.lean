import torus.shared.BosonFiniteCertificateNatFourRaiseSparse414
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates403P14

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

def f403desc12 : Matrix (Fin 54) (Fin 1) ℚ :=
  !![(1/2);
    (33/2);
    (159/2);
    (429/2);
    (663/2);
    (429/2);
    (-429/2);
    (-1287/2);
    165;
    1419;
    3300;
    3993;
    726;
    (-5445);
    (-4356);
    2637;
    9834;
    6765;
    (-9207);
    (-26532);
    5610;
    (-9405);
    (-48312);
    (-34650);
    (-29205);
    (-109494);
    (-23562);
    499;
    5742;
    11550;
    11055;
    (-1485);
    (-16236);
    19107;
    62700;
    37125;
    (-40392);
    (-42966);
    34650;
    (-19800);
    (-138600);
    (-79695);
    (-120582);
    18645;
    78705;
    38610;
    (-29106);
    91080;
    69300;
    (-8316);
    10395;
    46200;
    152460;
    75075]

theorem f403desc12_step : f414raise*f403desc11=f403desc12 := by
  refine natFourSparseRowProduct_matrix_check f414raise f403desc11 f403desc12
    f414raiseSparseRows f414_raise_sparse_rows_check ?_
  intro a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 0) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 1) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 2) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 3) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 4) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 5) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 6) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 7) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 8) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 9) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 10) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 11) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 12) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 13) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 14) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 15) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 16) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 17) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 18) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 19) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 20) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 21) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 22) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 23) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 24) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 25) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 26) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 27) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 28) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 29) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 30) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 31) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 32) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 33) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 34) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 35) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 36) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 37) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 38) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 39) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 40) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 41) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 42) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 43) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 44) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 45) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 46) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 47) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 48) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 49) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 50) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 51) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 52) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => natFourSparseRowProduct (f414raiseSparseRows 53) f403desc11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f403desc12 53 b)
      (by decide +kernel) 0 b

theorem f403desc12_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[12]
      (natFourWordBlock f403basis (complexify b403relative *ᵥ x))=
      natFourWordBlock f415basis (complexify f403desc12 *ᵥ x) := by
  exact natFour_descendant_step 11
    (fun x => natFourWordBlock f403basis (complexify b403relative *ᵥ x))
    f414basis f415basis f403desc11 f403desc12 f414raise
    f403desc11_actual f414_actual_raise_block f403desc12_step x

#print axioms f403desc12_step
#print axioms f403desc12_actual
end TorusLean.BosonFiniteCertificate
