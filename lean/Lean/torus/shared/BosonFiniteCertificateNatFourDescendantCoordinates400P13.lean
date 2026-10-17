import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates400P11

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

def f400desc12 : Matrix (Fin 34) (Fin 1) ℚ :=
  !![4;
    144;
    792;
    2640;
    5940;
    9504;
    5544;
    1584;
    15840;
    47520;
    95040;
    133056;
    35640;
    190080;
    332640;
    199584;
    221760;
    665280;
    138600;
    5280;
    71280;
    190080;
    332640;
    199584;
    285120;
    1330560;
    1995840;
    1330560;
    1663200;
    332640;
    1995840;
    1247400;
    3326400;
    369600]

theorem f400desc12_step : f411raise*f400desc11=f400desc12 := by
  decide +kernel

theorem f400desc12_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[12]
      (natFourWordBlock f400basis (complexify b400relative *ᵥ x))=
      natFourWordBlock f412basis (complexify f400desc12 *ᵥ x) := by
  exact natFour_descendant_step 11
    (fun x => natFourWordBlock f400basis (complexify b400relative *ᵥ x))
    f411basis f412basis f400desc11 f400desc12 f411raise
    f400desc11_actual f411_actual_raise_block f400desc12_step x

def f400desc13 : Matrix (Fin 39) (Fin 1) ℚ :=
  !![4;
    156;
    936;
    3432;
    8580;
    15444;
    20592;
    1872;
    20592;
    68640;
    154440;
    247104;
    144144;
    51480;
    308880;
    617760;
    864864;
    411840;
    1441440;
    864864;
    1081080;
    6864;
    102960;
    308880;
    617760;
    864864;
    463320;
    2471040;
    4324320;
    2594592;
    2882880;
    8648640;
    1801800;
    617760;
    4324320;
    6486480;
    8648640;
    10810800;
    4804800]

theorem f400desc13_step : f412raise*f400desc12=f400desc13 := by
  decide +kernel

theorem f400desc13_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[13]
      (natFourWordBlock f400basis (complexify b400relative *ᵥ x))=
      natFourWordBlock f413basis (complexify f400desc13 *ᵥ x) := by
  exact natFour_descendant_step 12
    (fun x => natFourWordBlock f400basis (complexify b400relative *ᵥ x))
    f412basis f413basis f400desc12 f400desc13 f412raise
    f400desc12_actual f412_actual_raise_block f400desc13_step x

#print axioms f400desc12_step
#print axioms f400desc12_actual
#print axioms f400desc13_step
#print axioms f400desc13_actual
end TorusLean.BosonFiniteCertificate
