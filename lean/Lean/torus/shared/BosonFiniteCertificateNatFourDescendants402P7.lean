import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates402
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger409
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

/-! Genuine Nat COM descendants of the original relative basis, with every
step checked against independently verified raising actions and every form
checked against independently reconstructed raw source M4 matrices. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

def f402desc7Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(617405125134742313204583014673/3906250000000000000000)]

private def f402desc7IntegerCoordinates : Matrix (Fin 18) (Fin 1) ℤ :=
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

private def f402desc7IntegerLeftProduct : Matrix (Fin 1) (Fin 18) ℤ :=
  !![0, 2984764090517460852340884480, (-129191867449414387545789021888), (-59959739514123295461388835712), (-215583004821971422518539300736), (-38825289704037433597586886720), (-75378036758097856459454917632), (-23077135304518878875375838048), (-92200836113020158068453496768), (-23242820433019188641006409120), (-36942013666691397674744434560), 23771252113805940272717577984, (-47305459430264469791095344000), (-5434624953965697005545381248), (-15367642786774515510654206784), (-22651147417454342912676587136), 33055805294587871765257049664, 13595621906023810976075231808]

private def f402desc7IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![158055712034494032180373251756288]

theorem f402desc7_compression_check :
    f402desc7ᵀ*f409rawM4Form*f402desc7=f402desc7Form := by
  have hD : natFourIntegerMatrix 1 f402desc7IntegerCoordinates=f402desc7 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f402desc7IntegerCoordinates) (f402desc7) (by decide +kernel) a b
  have hV : f402desc7IntegerCoordinatesᵀ*f409rawInteger=f402desc7IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 18) => (f402desc7IntegerCoordinatesᵀ*f409rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 18) => (f402desc7IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f402desc7IntegerLeftProduct*f402desc7IntegerCoordinates=f402desc7IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc7IntegerLeftProduct*f402desc7IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc7IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc7IntegerForm=f402desc7Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc7IntegerForm) (f402desc7Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f409rawInteger f402desc7IntegerCoordinates f402desc7IntegerLeftProduct f402desc7IntegerForm
    f409rawM4Form f402desc7 f402desc7Form f409_raw_integer_check hD hV hY hF

theorem f402desc7_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7] (natFourWordBlock f402basis (complexify b402relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7]
          (natFourWordBlock f402basis (complexify b402relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f402desc7Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 7
    f402basis b402relative
    f409basis f402desc7 f409rawM4Form f402desc7Form
    f402desc7_actual f409_actual_raw_M4_matrix f402desc7_compression_check x y


#print axioms f402desc7_compression_check
#print axioms f402desc7_source_form
end TorusLean.BosonFiniteCertificate
