import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRaise400
import torus.shared.BosonFiniteCertificateNatFourRaise401
import torus.shared.BosonFiniteCertificateNatFourRaise402
import torus.shared.BosonFiniteCertificateNatFourRaise403
import torus.shared.BosonFiniteCertificateNatFourRaise404
import torus.shared.BosonFiniteCertificateNatFourRaise405
import torus.shared.BosonFiniteCertificateNatFourRaise406
import torus.shared.BosonFiniteCertificateNatFourRaise407
import torus.shared.BosonFiniteCertificateNatFourRaise408
import torus.shared.BosonFiniteCertificateNatFourRaise409
import torus.shared.BosonFiniteCertificateNatFourRaise410
import torus.shared.BosonFiniteCertificateNatFourRaise411
import torus.shared.BosonFiniteCertificateNatFourRaise412
import torus.shared.BosonFiniteCertificateNatFourRaise413
import torus.shared.BosonFiniteCertificateNatFourRaise414
import torus.shared.BosonFiniteCertificateNatFourRaise415
import torus.shared.BosonFiniteCertificate400

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

def f400desc0 : Matrix (Fin 1) (Fin 1) ℚ :=
  !![1]

theorem f400desc0_root : f400desc0=b400relative := by
  decide +kernel

theorem f400desc0_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
      (natFourWordBlock f400basis (complexify b400relative *ᵥ x))=
      natFourWordBlock f400basis (complexify f400desc0 *ᵥ x) := by
  rw [Function.iterate_zero_apply,f400desc0_root]

def f400desc1 : Matrix (Fin 1) (Fin 1) ℚ :=
  !![4]

theorem f400desc1_step : f400raise*f400desc0=f400desc1 := by
  decide +kernel

theorem f400desc1_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
      (natFourWordBlock f400basis (complexify b400relative *ᵥ x))=
      natFourWordBlock f401basis (complexify f400desc1 *ᵥ x) := by
  exact natFour_descendant_step 0
    (fun x => natFourWordBlock f400basis (complexify b400relative *ᵥ x))
    f400basis f401basis f400desc0 f400desc1 f400raise
    f400desc0_actual f400_actual_raise_block f400desc1_step x

def f400desc2 : Matrix (Fin 2) (Fin 1) ℚ :=
  !![4;
    12]

theorem f400desc2_step : f401raise*f400desc1=f400desc2 := by
  decide +kernel

theorem f400desc2_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
      (natFourWordBlock f400basis (complexify b400relative *ᵥ x))=
      natFourWordBlock f402basis (complexify f400desc2 *ᵥ x) := by
  exact natFour_descendant_step 1
    (fun x => natFourWordBlock f400basis (complexify b400relative *ᵥ x))
    f401basis f402basis f400desc1 f400desc2 f401raise
    f400desc1_actual f401_actual_raise_block f400desc2_step x

def f400desc3 : Matrix (Fin 3) (Fin 1) ℚ :=
  !![4;
    36;
    24]

theorem f400desc3_step : f402raise*f400desc2=f400desc3 := by
  decide +kernel

theorem f400desc3_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
      (natFourWordBlock f400basis (complexify b400relative *ᵥ x))=
      natFourWordBlock f403basis (complexify f400desc3 *ᵥ x) := by
  exact natFour_descendant_step 2
    (fun x => natFourWordBlock f400basis (complexify b400relative *ᵥ x))
    f402basis f403basis f400desc2 f400desc3 f402raise
    f400desc2_actual f402_actual_raise_block f400desc3_step x

def f400desc4 : Matrix (Fin 5) (Fin 1) ℚ :=
  !![4;
    48;
    36;
    144;
    24]

theorem f400desc4_step : f403raise*f400desc3=f400desc4 := by
  decide +kernel

theorem f400desc4_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
      (natFourWordBlock f400basis (complexify b400relative *ᵥ x))=
      natFourWordBlock f404basis (complexify f400desc4 *ᵥ x) := by
  exact natFour_descendant_step 3
    (fun x => natFourWordBlock f400basis (complexify b400relative *ᵥ x))
    f403basis f404basis f400desc3 f400desc4 f403raise
    f400desc3_actual f403_actual_raise_block f400desc4_step x

def f400desc5 : Matrix (Fin 6) (Fin 1) ℚ :=
  !![4;
    60;
    120;
    240;
    360;
    240]

theorem f400desc5_step : f404raise*f400desc4=f400desc5 := by
  decide +kernel

theorem f400desc5_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
      (natFourWordBlock f400basis (complexify b400relative *ᵥ x))=
      natFourWordBlock f405basis (complexify f400desc5 *ᵥ x) := by
  exact natFour_descendant_step 4
    (fun x => natFourWordBlock f400basis (complexify b400relative *ᵥ x))
    f404basis f405basis f400desc4 f400desc5 f404raise
    f400desc4_actual f404_actual_raise_block f400desc5_step x

def f400desc6 : Matrix (Fin 9) (Fin 1) ℚ :=
  !![4;
    72;
    180;
    120;
    360;
    1440;
    360;
    480;
    1080]

theorem f400desc6_step : f405raise*f400desc5=f400desc6 := by
  decide +kernel

theorem f400desc6_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6]
      (natFourWordBlock f400basis (complexify b400relative *ᵥ x))=
      natFourWordBlock f406basis (complexify f400desc6 *ᵥ x) := by
  exact natFour_descendant_step 5
    (fun x => natFourWordBlock f400basis (complexify b400relative *ᵥ x))
    f405basis f406basis f400desc5 f400desc6 f405raise
    f400desc5_actual f405_actual_raise_block f400desc6_step x

def f400desc7 : Matrix (Fin 11) (Fin 1) ℚ :=
  !![4;
    84;
    252;
    420;
    504;
    2520;
    1680;
    2520;
    840;
    5040;
    2520]

theorem f400desc7_step : f406raise*f400desc6=f400desc7 := by
  decide +kernel

theorem f400desc7_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7]
      (natFourWordBlock f400basis (complexify b400relative *ᵥ x))=
      natFourWordBlock f407basis (complexify f400desc7 *ᵥ x) := by
  exact natFour_descendant_step 6
    (fun x => natFourWordBlock f400basis (complexify b400relative *ᵥ x))
    f406basis f407basis f400desc6 f400desc7 f406raise
    f400desc6_actual f406_actual_raise_block f400desc7_step x

#print axioms f400desc0_root
#print axioms f400desc0_actual
#print axioms f400desc1_step
#print axioms f400desc1_actual
#print axioms f400desc2_step
#print axioms f400desc2_actual
#print axioms f400desc3_step
#print axioms f400desc3_actual
#print axioms f400desc4_step
#print axioms f400desc4_actual
#print axioms f400desc5_step
#print axioms f400desc5_actual
#print axioms f400desc6_step
#print axioms f400desc6_actual
#print axioms f400desc7_step
#print axioms f400desc7_actual
end TorusLean.BosonFiniteCertificate
