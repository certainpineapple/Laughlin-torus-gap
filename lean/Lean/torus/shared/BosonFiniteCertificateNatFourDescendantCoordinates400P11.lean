import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates400P07

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

def f400desc8 : Matrix (Fin 15) (Fin 1) ℚ :=
  !![4;
    96;
    336;
    672;
    420;
    672;
    4032;
    6720;
    5040;
    6720;
    1344;
    10080;
    6720;
    20160;
    2520]

theorem f400desc8_step : f407raise*f400desc7=f400desc8 := by
  decide +kernel

theorem f400desc8_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8]
      (natFourWordBlock f400basis (complexify b400relative *ᵥ x))=
      natFourWordBlock f408basis (complexify f400desc8 *ᵥ x) := by
  exact natFour_descendant_step 7
    (fun x => natFourWordBlock f400basis (complexify b400relative *ᵥ x))
    f407basis f408basis f400desc7 f400desc8 f407raise
    f400desc7_actual f407_actual_raise_block f400desc8_step x

def f400desc9 : Matrix (Fin 18) (Fin 1) ℚ :=
  !![4;
    108;
    432;
    1008;
    1512;
    864;
    6048;
    12096;
    7560;
    9072;
    30240;
    6720;
    2016;
    18144;
    30240;
    45360;
    60480;
    30240]

theorem f400desc9_step : f408raise*f400desc8=f400desc9 := by
  decide +kernel

theorem f400desc9_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[9]
      (natFourWordBlock f400basis (complexify b400relative *ᵥ x))=
      natFourWordBlock f409basis (complexify f400desc9 *ᵥ x) := by
  exact natFour_descendant_step 8
    (fun x => natFourWordBlock f400basis (complexify b400relative *ᵥ x))
    f408basis f409basis f400desc8 f400desc9 f408raise
    f400desc8_actual f408_actual_raise_block f400desc9_step x

def f400desc10 : Matrix (Fin 23) (Fin 1) ℚ :=
  !![4;
    120;
    540;
    1440;
    2520;
    1512;
    1080;
    8640;
    20160;
    30240;
    15120;
    60480;
    37800;
    50400;
    2880;
    30240;
    60480;
    37800;
    90720;
    302400;
    67200;
    75600;
    151200]

theorem f400desc10_step : f409raise*f400desc9=f400desc10 := by
  decide +kernel

theorem f400desc10_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[10]
      (natFourWordBlock f400basis (complexify b400relative *ᵥ x))=
      natFourWordBlock f410basis (complexify f400desc10 *ᵥ x) := by
  exact natFour_descendant_step 9
    (fun x => natFourWordBlock f400basis (complexify b400relative *ᵥ x))
    f409basis f410basis f400desc9 f400desc10 f409raise
    f400desc9_actual f409_actual_raise_block f400desc10_step x

def f400desc11 : Matrix (Fin 27) (Fin 1) ℚ :=
  !![4;
    132;
    660;
    1980;
    3960;
    5544;
    1320;
    11880;
    31680;
    55440;
    33264;
    23760;
    110880;
    166320;
    110880;
    138600;
    3960;
    47520;
    110880;
    166320;
    166320;
    665280;
    415800;
    554400;
    166320;
    831600;
    369600]

theorem f400desc11_step : f410raise*f400desc10=f400desc11 := by
  decide +kernel

theorem f400desc11_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[11]
      (natFourWordBlock f400basis (complexify b400relative *ᵥ x))=
      natFourWordBlock f411basis (complexify f400desc11 *ᵥ x) := by
  exact natFour_descendant_step 10
    (fun x => natFourWordBlock f400basis (complexify b400relative *ᵥ x))
    f410basis f411basis f400desc10 f400desc11 f410raise
    f400desc10_actual f410_actual_raise_block f400desc11_step x

#print axioms f400desc8_step
#print axioms f400desc8_actual
#print axioms f400desc9_step
#print axioms f400desc9_actual
#print axioms f400desc10_step
#print axioms f400desc10_actual
#print axioms f400desc11_step
#print axioms f400desc11_actual
end TorusLean.BosonFiniteCertificate
