import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates402P11

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

def f402desc10 : Matrix (Fin 34) (Fin 1) ℚ :=
  !![(-1);
    (-28);
    (-118);
    (-300);
    (-525);
    (-696);
    (-378);
    (-228);
    (-1640);
    (-3480);
    (-5040);
    (-5712);
    (-2430);
    (-8160);
    (-9240);
    (-4536);
    (-5040);
    (-8400);
    (-1050);
    (-520);
    (-4500);
    (-7200);
    (-7560);
    (-3528);
    (-9360);
    (-16800);
    (-5040);
    3360;
    12600;
    (-2520);
    15120;
    15750;
    58800;
    8400]

theorem f402desc10_step : f411raise*f402desc9=f402desc10 := by
  decide +kernel

theorem f402desc10_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[10]
      (natFourWordBlock f402basis (complexify b402relative *ᵥ x))=
      natFourWordBlock f412basis (complexify f402desc10 *ᵥ x) := by
  exact natFour_descendant_step 9
    (fun x => natFourWordBlock f402basis (complexify b402relative *ᵥ x))
    f411basis f412basis f402desc9 f402desc10 f411raise
    f402desc9_actual f411_actual_raise_block f402desc10_step x

def f402desc11 : Matrix (Fin 39) (Fin 1) ℚ :=
  !![(-1);
    (-31);
    (-146);
    (-418);
    (-825);
    (-1221);
    (-1452);
    (-284);
    (-2332);
    (-5720);
    (-9570);
    (-12144);
    (-6468);
    (-4070);
    (-16500);
    (-22440);
    (-24024);
    (-13200);
    (-27720);
    (-12936);
    (-11550);
    (-748);
    (-7700);
    (-15180);
    (-19800);
    (-20328);
    (-20790);
    (-58080);
    (-46200);
    (-16632);
    (-18480);
    18480;
    11550;
    (-11880);
    (-9240);
    41580;
    92400;
    161700;
    92400]

theorem f402desc11_step : f412raise*f402desc10=f402desc11 := by
  decide +kernel

theorem f402desc11_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[11]
      (natFourWordBlock f402basis (complexify b402relative *ᵥ x))=
      natFourWordBlock f413basis (complexify f402desc11 *ᵥ x) := by
  exact natFour_descendant_step 10
    (fun x => natFourWordBlock f402basis (complexify b402relative *ᵥ x))
    f412basis f413basis f402desc10 f402desc11 f412raise
    f402desc10_actual f412_actual_raise_block f402desc11_step x

#print axioms f402desc10_step
#print axioms f402desc10_actual
#print axioms f402desc11_step
#print axioms f402desc11_actual
end TorusLean.BosonFiniteCertificate
