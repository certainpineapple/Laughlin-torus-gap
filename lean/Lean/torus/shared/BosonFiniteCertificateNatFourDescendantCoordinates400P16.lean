import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates400P15

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

def f400desc16 : Matrix (Fin 64) (Fin 1) ℚ :=
  !![4;
    192;
    1440;
    6720;
    21840;
    52416;
    96096;
    137280;
    77220;
    2880;
    40320;
    174720;
    524160;
    1153152;
    1921920;
    2471040;
    131040;
    1048320;
    2882880;
    5765760;
    8648640;
    4942080;
    1921920;
    9609600;
    17297280;
    23063040;
    10810800;
    34594560;
    20180160;
    24216192;
    13440;
    262080;
    1048320;
    2882880;
    5765760;
    8648640;
    4942080;
    1572480;
    11531520;
    28828800;
    51891840;
    69189120;
    19219200;
    86486400;
    138378240;
    80720640;
    86486400;
    242161920;
    48432384;
    2882880;
    28828800;
    64864800;
    103783680;
    60540480;
    86486400;
    345945600;
    484323840;
    302702400;
    363242880;
    76876800;
    403603200;
    242161920;
    605404800;
    63063000]

theorem f400desc16_step : f415raise*f400desc15=f400desc16 := by
  ext a b
  fin_cases a
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 0 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 0 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 1 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 1 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 2 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 2 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 3 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 3 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 4 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 4 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 5 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 5 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 6 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 6 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 7 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 7 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 8 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 8 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 9 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 9 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 10 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 10 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 11 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 11 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 12 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 12 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 13 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 13 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 14 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 14 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 15 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 15 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 16 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 16 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 17 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 17 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 18 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 18 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 19 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 19 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 20 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 20 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 21 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 21 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 22 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 22 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 23 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 23 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 24 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 24 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 25 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 25 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 26 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 26 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 27 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 27 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 28 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 28 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 29 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 29 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 30 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 30 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 31 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 31 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 32 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 32 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 33 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 33 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 34 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 34 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 35 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 35 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 36 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 36 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 37 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 37 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 38 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 38 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 39 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 39 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 40 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 40 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 41 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 41 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 42 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 42 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 43 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 43 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 44 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 44 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 45 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 45 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 46 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 46 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 47 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 47 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 48 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 48 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 49 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 49 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 50 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 50 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 51 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 51 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 52 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 52 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 53 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 53 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 54 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 54 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 55 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 55 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 56 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 56 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 57 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 57 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 58 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 58 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 59 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 59 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 60 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 60 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 61 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 61 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 62 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 62 b)
      (by decide +kernel) 0 b
  · exact natFourRationalEntryCheck_sound
      (fun (_ : Fin 1) (b : Fin 1) => (f415raise*f400desc15) 63 b)
      (fun (_ : Fin 1) (b : Fin 1) => f400desc16 63 b)
      (by decide +kernel) 0 b

theorem f400desc16_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[16]
      (natFourWordBlock f400basis (complexify b400relative *ᵥ x))=
      natFourWordBlock f416basis (complexify f400desc16 *ᵥ x) := by
  exact natFour_descendant_step 15
    (fun x => natFourWordBlock f400basis (complexify b400relative *ᵥ x))
    f415basis f416basis f400desc15 f400desc16 f415raise
    f400desc15_actual f415_actual_raise_block f400desc16_step x

#print axioms f400desc16_step
#print axioms f400desc16_actual
end TorusLean.BosonFiniteCertificate
