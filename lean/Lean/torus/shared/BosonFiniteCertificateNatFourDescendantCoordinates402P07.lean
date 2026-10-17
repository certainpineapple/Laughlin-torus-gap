import torus.shared.BosonFiniteCertificateNatFourDescendantCore
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
import torus.shared.BosonFiniteCertificate402

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

def f402desc0 : Matrix (Fin 2) (Fin 1) ℚ :=
  !![(-1);
    1]

theorem f402desc0_root : f402desc0=b402relative := by
  decide +kernel

theorem f402desc0_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
      (natFourWordBlock f402basis (complexify b402relative *ᵥ x))=
      natFourWordBlock f402basis (complexify f402desc0 *ᵥ x) := by
  rw [Function.iterate_zero_apply,f402desc0_root]

def f402desc1 : Matrix (Fin 3) (Fin 1) ℚ :=
  !![(-1);
    (-1);
    2]

theorem f402desc1_step : f402raise*f402desc0=f402desc1 := by
  decide +kernel

theorem f402desc1_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
      (natFourWordBlock f402basis (complexify b402relative *ᵥ x))=
      natFourWordBlock f403basis (complexify f402desc1 *ᵥ x) := by
  exact natFour_descendant_step 0
    (fun x => natFourWordBlock f402basis (complexify b402relative *ᵥ x))
    f402basis f403basis f402desc0 f402desc1 f402raise
    f402desc0_actual f402_actual_raise_block f402desc1_step x

def f402desc2 : Matrix (Fin 5) (Fin 1) ℚ :=
  !![(-1);
    (-4);
    (-1);
    4;
    2]

theorem f402desc2_step : f403raise*f402desc1=f402desc2 := by
  decide +kernel

theorem f402desc2_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
      (natFourWordBlock f402basis (complexify b402relative *ᵥ x))=
      natFourWordBlock f404basis (complexify f402desc2 *ᵥ x) := by
  exact natFour_descendant_step 1
    (fun x => natFourWordBlock f402basis (complexify b402relative *ᵥ x))
    f403basis f404basis f402desc1 f402desc2 f403raise
    f402desc1_actual f403_actual_raise_block f402desc2_step x

def f402desc3 : Matrix (Fin 6) (Fin 1) ℚ :=
  !![(-1);
    (-7);
    (-6);
    (-4);
    6;
    12]

theorem f402desc3_step : f404raise*f402desc2=f402desc3 := by
  decide +kernel

theorem f402desc3_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
      (natFourWordBlock f402basis (complexify b402relative *ᵥ x))=
      natFourWordBlock f405basis (complexify f402desc3 *ᵥ x) := by
  exact natFour_descendant_step 2
    (fun x => natFourWordBlock f402basis (complexify b402relative *ᵥ x))
    f404basis f405basis f402desc2 f402desc3 f404raise
    f402desc2_actual f404_actual_raise_block f402desc3_step x

def f402desc4 : Matrix (Fin 9) (Fin 1) ℚ :=
  !![(-1);
    (-10);
    (-13);
    (-6);
    (-18);
    (-8);
    6;
    8;
    42]

theorem f402desc4_step : f405raise*f402desc3=f402desc4 := by
  decide +kernel

theorem f402desc4_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
      (natFourWordBlock f402basis (complexify b402relative *ᵥ x))=
      natFourWordBlock f406basis (complexify f402desc4 *ᵥ x) := by
  exact natFour_descendant_step 3
    (fun x => natFourWordBlock f402basis (complexify b402relative *ᵥ x))
    f405basis f406basis f402desc3 f402desc4 f405raise
    f402desc3_actual f405_actual_raise_block f402desc4_step x

def f402desc5 : Matrix (Fin 11) (Fin 1) ℚ :=
  !![(-1);
    (-13);
    (-23);
    (-25);
    (-38);
    (-70);
    (-20);
    10;
    (-10);
    100;
    90]

theorem f402desc5_step : f406raise*f402desc4=f402desc5 := by
  decide +kernel

theorem f402desc5_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
      (natFourWordBlock f402basis (complexify b402relative *ᵥ x))=
      natFourWordBlock f407basis (complexify f402desc5 *ᵥ x) := by
  exact natFour_descendant_step 4
    (fun x => natFourWordBlock f402basis (complexify b402relative *ᵥ x))
    f406basis f407basis f402desc4 f402desc5 f406raise
    f402desc4_actual f406_actual_raise_block f402desc5_step x

#print axioms f402desc0_root
#print axioms f402desc0_actual
#print axioms f402desc1_step
#print axioms f402desc1_actual
#print axioms f402desc2_step
#print axioms f402desc2_actual
#print axioms f402desc3_step
#print axioms f402desc3_actual
#print axioms f402desc4_step
#print axioms f402desc4_actual
#print axioms f402desc5_step
#print axioms f402desc5_actual
end TorusLean.BosonFiniteCertificate
