import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates402P07

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

def f402desc6 : Matrix (Fin 15) (Fin 1) ℚ :=
  !![(-1);
    (-16);
    (-36);
    (-48);
    (-25);
    (-64);
    (-192);
    (-160);
    (-60);
    0;
    (-48);
    0;
    80;
    480;
    90]

theorem f402desc6_step : f407raise*f402desc5=f402desc6 := by
  decide +kernel

theorem f402desc6_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6]
      (natFourWordBlock f402basis (complexify b402relative *ᵥ x))=
      natFourWordBlock f408basis (complexify f402desc6 *ᵥ x) := by
  exact natFour_descendant_step 5
    (fun x => natFourWordBlock f402basis (complexify b402relative *ᵥ x))
    f407basis f408basis f402desc5 f402desc6 f407raise
    f402desc5_actual f407_actual_raise_block f402desc6_step x

def f402desc7 : Matrix (Fin 18) (Fin 1) ℚ :=
  !![(-1);
    (-19);
    (-52);
    (-84);
    (-98);
    (-96);
    (-392);
    (-448);
    (-210);
    (-252);
    (-280);
    0;
    (-112);
    (-336);
    0;
    420;
    1120;
    840]

theorem f402desc7_step : f408raise*f402desc6=f402desc7 := by
  decide +kernel

theorem f402desc7_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7]
      (natFourWordBlock f402basis (complexify b402relative *ᵥ x))=
      natFourWordBlock f409basis (complexify f402desc7 *ᵥ x) := by
  exact natFour_descendant_step 6
    (fun x => natFourWordBlock f402basis (complexify b402relative *ᵥ x))
    f408basis f409basis f402desc6 f402desc7 f408raise
    f402desc6_actual f408_actual_raise_block f402desc7_step x

def f402desc8 : Matrix (Fin 23) (Fin 1) ℚ :=
  !![(-1);
    (-22);
    (-71);
    (-136);
    (-182);
    (-98);
    (-134);
    (-688);
    (-1008);
    (-1064);
    (-644);
    (-1232);
    (-490);
    (-280);
    (-208);
    (-1064);
    (-784);
    (-210);
    (-504);
    2800;
    1120;
    1260;
    3640]

theorem f402desc8_step : f409raise*f402desc7=f402desc8 := by
  decide +kernel

theorem f402desc8_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8]
      (natFourWordBlock f402basis (complexify b402relative *ᵥ x))=
      natFourWordBlock f410basis (complexify f402desc8 *ᵥ x) := by
  exact natFour_descendant_step 7
    (fun x => natFourWordBlock f402basis (complexify b402relative *ᵥ x))
    f409basis f410basis f402desc7 f402desc8 f409raise
    f402desc7_actual f409_actual_raise_block f402desc8_step x

def f402desc9 : Matrix (Fin 27) (Fin 1) ℚ :=
  !![(-1);
    (-25);
    (-93);
    (-207);
    (-318);
    (-378);
    (-178);
    (-1098);
    (-1968);
    (-2436);
    (-1260);
    (-1332);
    (-3528);
    (-3276);
    (-1512);
    (-1050);
    (-342);
    (-2376);
    (-2856);
    (-2268);
    (-3276);
    (-1008);
    1890;
    5880;
    756;
    13860;
    8400]

theorem f402desc9_step : f410raise*f402desc8=f402desc9 := by
  decide +kernel

theorem f402desc9_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[9]
      (natFourWordBlock f402basis (complexify b402relative *ᵥ x))=
      natFourWordBlock f411basis (complexify f402desc9 *ᵥ x) := by
  exact natFour_descendant_step 8
    (fun x => natFourWordBlock f402basis (complexify b402relative *ᵥ x))
    f410basis f411basis f402desc8 f402desc9 f410raise
    f402desc8_actual f410_actual_raise_block f402desc9_step x

#print axioms f402desc6_step
#print axioms f402desc6_actual
#print axioms f402desc7_step
#print axioms f402desc7_actual
#print axioms f402desc8_step
#print axioms f402desc8_actual
#print axioms f402desc9_step
#print axioms f402desc9_actual
end TorusLean.BosonFiniteCertificate
