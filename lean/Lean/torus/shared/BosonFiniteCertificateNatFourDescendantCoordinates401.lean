import torus.shared.BosonFiniteCertificateNatFourDescendantCore
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
import torus.shared.BosonFiniteCertificate401

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

def f401desc0 : Matrix (Fin 1) (Fin 0) ℚ :=
  fun _ _ => 0

theorem f401desc0_root : f401desc0=b401relative := by
  decide +kernel

theorem f401desc0_actual (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
      (natFourWordBlock f401basis (complexify b401relative *ᵥ x))=
      natFourWordBlock f401basis (complexify f401desc0 *ᵥ x) := by
  rw [Function.iterate_zero_apply,f401desc0_root]

def f401desc1 : Matrix (Fin 2) (Fin 0) ℚ :=
  fun _ _ => 0

theorem f401desc1_step : f401raise*f401desc0=f401desc1 := by
  decide +kernel

theorem f401desc1_actual (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
      (natFourWordBlock f401basis (complexify b401relative *ᵥ x))=
      natFourWordBlock f402basis (complexify f401desc1 *ᵥ x) := by
  exact natFour_descendant_step 0
    (fun x => natFourWordBlock f401basis (complexify b401relative *ᵥ x))
    f401basis f402basis f401desc0 f401desc1 f401raise
    f401desc0_actual f401_actual_raise_block f401desc1_step x

def f401desc2 : Matrix (Fin 3) (Fin 0) ℚ :=
  fun _ _ => 0

theorem f401desc2_step : f402raise*f401desc1=f401desc2 := by
  decide +kernel

theorem f401desc2_actual (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
      (natFourWordBlock f401basis (complexify b401relative *ᵥ x))=
      natFourWordBlock f403basis (complexify f401desc2 *ᵥ x) := by
  exact natFour_descendant_step 1
    (fun x => natFourWordBlock f401basis (complexify b401relative *ᵥ x))
    f402basis f403basis f401desc1 f401desc2 f402raise
    f401desc1_actual f402_actual_raise_block f401desc2_step x

def f401desc3 : Matrix (Fin 5) (Fin 0) ℚ :=
  fun _ _ => 0

theorem f401desc3_step : f403raise*f401desc2=f401desc3 := by
  decide +kernel

theorem f401desc3_actual (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
      (natFourWordBlock f401basis (complexify b401relative *ᵥ x))=
      natFourWordBlock f404basis (complexify f401desc3 *ᵥ x) := by
  exact natFour_descendant_step 2
    (fun x => natFourWordBlock f401basis (complexify b401relative *ᵥ x))
    f403basis f404basis f401desc2 f401desc3 f403raise
    f401desc2_actual f403_actual_raise_block f401desc3_step x

def f401desc4 : Matrix (Fin 6) (Fin 0) ℚ :=
  fun _ _ => 0

theorem f401desc4_step : f404raise*f401desc3=f401desc4 := by
  decide +kernel

theorem f401desc4_actual (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
      (natFourWordBlock f401basis (complexify b401relative *ᵥ x))=
      natFourWordBlock f405basis (complexify f401desc4 *ᵥ x) := by
  exact natFour_descendant_step 3
    (fun x => natFourWordBlock f401basis (complexify b401relative *ᵥ x))
    f404basis f405basis f401desc3 f401desc4 f404raise
    f401desc3_actual f404_actual_raise_block f401desc4_step x

def f401desc5 : Matrix (Fin 9) (Fin 0) ℚ :=
  fun _ _ => 0

theorem f401desc5_step : f405raise*f401desc4=f401desc5 := by
  decide +kernel

theorem f401desc5_actual (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
      (natFourWordBlock f401basis (complexify b401relative *ᵥ x))=
      natFourWordBlock f406basis (complexify f401desc5 *ᵥ x) := by
  exact natFour_descendant_step 4
    (fun x => natFourWordBlock f401basis (complexify b401relative *ᵥ x))
    f405basis f406basis f401desc4 f401desc5 f405raise
    f401desc4_actual f405_actual_raise_block f401desc5_step x

def f401desc6 : Matrix (Fin 11) (Fin 0) ℚ :=
  fun _ _ => 0

theorem f401desc6_step : f406raise*f401desc5=f401desc6 := by
  decide +kernel

theorem f401desc6_actual (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6]
      (natFourWordBlock f401basis (complexify b401relative *ᵥ x))=
      natFourWordBlock f407basis (complexify f401desc6 *ᵥ x) := by
  exact natFour_descendant_step 5
    (fun x => natFourWordBlock f401basis (complexify b401relative *ᵥ x))
    f406basis f407basis f401desc5 f401desc6 f406raise
    f401desc5_actual f406_actual_raise_block f401desc6_step x

def f401desc7 : Matrix (Fin 15) (Fin 0) ℚ :=
  fun _ _ => 0

theorem f401desc7_step : f407raise*f401desc6=f401desc7 := by
  decide +kernel

theorem f401desc7_actual (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7]
      (natFourWordBlock f401basis (complexify b401relative *ᵥ x))=
      natFourWordBlock f408basis (complexify f401desc7 *ᵥ x) := by
  exact natFour_descendant_step 6
    (fun x => natFourWordBlock f401basis (complexify b401relative *ᵥ x))
    f407basis f408basis f401desc6 f401desc7 f407raise
    f401desc6_actual f407_actual_raise_block f401desc7_step x

def f401desc8 : Matrix (Fin 18) (Fin 0) ℚ :=
  fun _ _ => 0

theorem f401desc8_step : f408raise*f401desc7=f401desc8 := by
  decide +kernel

theorem f401desc8_actual (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8]
      (natFourWordBlock f401basis (complexify b401relative *ᵥ x))=
      natFourWordBlock f409basis (complexify f401desc8 *ᵥ x) := by
  exact natFour_descendant_step 7
    (fun x => natFourWordBlock f401basis (complexify b401relative *ᵥ x))
    f408basis f409basis f401desc7 f401desc8 f408raise
    f401desc7_actual f408_actual_raise_block f401desc8_step x

def f401desc9 : Matrix (Fin 23) (Fin 0) ℚ :=
  fun _ _ => 0

theorem f401desc9_step : f409raise*f401desc8=f401desc9 := by
  decide +kernel

theorem f401desc9_actual (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[9]
      (natFourWordBlock f401basis (complexify b401relative *ᵥ x))=
      natFourWordBlock f410basis (complexify f401desc9 *ᵥ x) := by
  exact natFour_descendant_step 8
    (fun x => natFourWordBlock f401basis (complexify b401relative *ᵥ x))
    f409basis f410basis f401desc8 f401desc9 f409raise
    f401desc8_actual f409_actual_raise_block f401desc9_step x

def f401desc10 : Matrix (Fin 27) (Fin 0) ℚ :=
  fun _ _ => 0

theorem f401desc10_step : f410raise*f401desc9=f401desc10 := by
  decide +kernel

theorem f401desc10_actual (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[10]
      (natFourWordBlock f401basis (complexify b401relative *ᵥ x))=
      natFourWordBlock f411basis (complexify f401desc10 *ᵥ x) := by
  exact natFour_descendant_step 9
    (fun x => natFourWordBlock f401basis (complexify b401relative *ᵥ x))
    f410basis f411basis f401desc9 f401desc10 f410raise
    f401desc9_actual f410_actual_raise_block f401desc10_step x

def f401desc11 : Matrix (Fin 34) (Fin 0) ℚ :=
  fun _ _ => 0

theorem f401desc11_step : f411raise*f401desc10=f401desc11 := by
  decide +kernel

theorem f401desc11_actual (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[11]
      (natFourWordBlock f401basis (complexify b401relative *ᵥ x))=
      natFourWordBlock f412basis (complexify f401desc11 *ᵥ x) := by
  exact natFour_descendant_step 10
    (fun x => natFourWordBlock f401basis (complexify b401relative *ᵥ x))
    f411basis f412basis f401desc10 f401desc11 f411raise
    f401desc10_actual f411_actual_raise_block f401desc11_step x

def f401desc12 : Matrix (Fin 39) (Fin 0) ℚ :=
  fun _ _ => 0

theorem f401desc12_step : f412raise*f401desc11=f401desc12 := by
  decide +kernel

theorem f401desc12_actual (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[12]
      (natFourWordBlock f401basis (complexify b401relative *ᵥ x))=
      natFourWordBlock f413basis (complexify f401desc12 *ᵥ x) := by
  exact natFour_descendant_step 11
    (fun x => natFourWordBlock f401basis (complexify b401relative *ᵥ x))
    f412basis f413basis f401desc11 f401desc12 f412raise
    f401desc11_actual f412_actual_raise_block f401desc12_step x

def f401desc13 : Matrix (Fin 47) (Fin 0) ℚ :=
  fun _ _ => 0

theorem f401desc13_step : f413raise*f401desc12=f401desc13 := by
  decide +kernel

theorem f401desc13_actual (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[13]
      (natFourWordBlock f401basis (complexify b401relative *ᵥ x))=
      natFourWordBlock f414basis (complexify f401desc13 *ᵥ x) := by
  exact natFour_descendant_step 12
    (fun x => natFourWordBlock f401basis (complexify b401relative *ᵥ x))
    f413basis f414basis f401desc12 f401desc13 f413raise
    f401desc12_actual f413_actual_raise_block f401desc13_step x

def f401desc14 : Matrix (Fin 54) (Fin 0) ℚ :=
  fun _ _ => 0

theorem f401desc14_step : f414raise*f401desc13=f401desc14 := by
  decide +kernel

theorem f401desc14_actual (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[14]
      (natFourWordBlock f401basis (complexify b401relative *ᵥ x))=
      natFourWordBlock f415basis (complexify f401desc14 *ᵥ x) := by
  exact natFour_descendant_step 13
    (fun x => natFourWordBlock f401basis (complexify b401relative *ᵥ x))
    f414basis f415basis f401desc13 f401desc14 f414raise
    f401desc13_actual f414_actual_raise_block f401desc14_step x

def f401desc15 : Matrix (Fin 64) (Fin 0) ℚ :=
  fun _ _ => 0

theorem f401desc15_step : f415raise*f401desc14=f401desc15 := by
  decide +kernel

theorem f401desc15_actual (x : Fin 0 → ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[15]
      (natFourWordBlock f401basis (complexify b401relative *ᵥ x))=
      natFourWordBlock f416basis (complexify f401desc15 *ᵥ x) := by
  exact natFour_descendant_step 14
    (fun x => natFourWordBlock f401basis (complexify b401relative *ᵥ x))
    f415basis f416basis f401desc14 f401desc15 f415raise
    f401desc14_actual f415_actual_raise_block f401desc15_step x

#print axioms f401desc0_root
#print axioms f401desc0_actual
#print axioms f401desc1_step
#print axioms f401desc1_actual
#print axioms f401desc2_step
#print axioms f401desc2_actual
#print axioms f401desc3_step
#print axioms f401desc3_actual
#print axioms f401desc4_step
#print axioms f401desc4_actual
#print axioms f401desc5_step
#print axioms f401desc5_actual
#print axioms f401desc6_step
#print axioms f401desc6_actual
#print axioms f401desc7_step
#print axioms f401desc7_actual
#print axioms f401desc8_step
#print axioms f401desc8_actual
#print axioms f401desc9_step
#print axioms f401desc9_actual
#print axioms f401desc10_step
#print axioms f401desc10_actual
#print axioms f401desc11_step
#print axioms f401desc11_actual
#print axioms f401desc12_step
#print axioms f401desc12_actual
#print axioms f401desc13_step
#print axioms f401desc13_actual
#print axioms f401desc14_step
#print axioms f401desc14_actual
#print axioms f401desc15_step
#print axioms f401desc15_actual
end TorusLean.BosonFiniteCertificate
