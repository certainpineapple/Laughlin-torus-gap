import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates404
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger409
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
import torus.shared.BosonFiniteCertificate404

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

def f404desc5Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(663858144560211020749802783/1464843750000000000000), (-3171052257075898413196599073/46875000000000000000000);
    (-3171052257075898413196599073/46875000000000000000000), (437311207870200287718010967/937500000000000000000)]

private def f404desc5IntegerCoordinates : Matrix (Fin 18) (Fin 2) ℤ :=
  !![1, (-1);
    11, (-11);
    16, (-10);
    16, 14;
    18, 42;
    20, (-26);
    0, (-12);
    (-8), 68;
    10, 50;
    (-24), (-30);
    80, (-260);
    40, (-100);
    (-20), 2;
    (-180), 114;
    (-100), 130;
    (-120), 90;
    120, (-60);
    120, 0]

private def f404desc5IntegerLeftProduct : Matrix (Fin 2) (Fin 18) ℤ :=
  !![0, (-14461524240271660030157554560), (-14917174179584361053027226432), 24284117219452717748688264384, 32499136126848567850993159680, 4679368747492332427931050560, (-285711119185862380363938048), 5619612366812716147028236320, 4486059836395890514043072448, (-5539838292583832716614768480), 3638480445168226850246772864, 10643567473981963413629009280, 674996354840465585937313920, (-4790451156668838543843230592), 560663120857964909421307776, (-4805009257316301532337151360), 6029014966565874835281472320, 3890828867017150414487051136;
    0, (-6897332253774787393727928000), 2554518448537413521869038912, 1614723830041231997450146656, 50755095044116722102118788672, (-3929902559854189518988296000), (-4788938993086732896090120192), (-1422618964644254747895714240), 9997787219415971734007709504, (-1869966681050123979356088480), 95755846917137284940953344, (-11341971487363788354889414080), (-5108002944494318552570152320), 788854002658223861351603712, (-3616994150532282468986913120), 3087251973064230382014082176, (-6299826275599931939169264000), (-2835907589679969946354265376)]

private def f404desc5IntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![4078744440177936511486788298752, (-608842033358572495333747022016);
    (-608842033358572495333747022016), 4198187595553922762092905283200]

theorem f404desc5_compression_check :
    f404desc5ᵀ*f409rawM4Form*f404desc5=f404desc5Form := by
  have hD : natFourIntegerMatrix 3 f404desc5IntegerCoordinates=f404desc5 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 3 f404desc5IntegerCoordinates) (f404desc5) (by decide +kernel) a b
  have hV : f404desc5IntegerCoordinatesᵀ*f409rawInteger=f404desc5IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 18) => (f404desc5IntegerCoordinatesᵀ*f409rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 18) => (f404desc5IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 18) => (f404desc5IntegerCoordinatesᵀ*f409rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 18) => (f404desc5IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f404desc5IntegerLeftProduct*f404desc5IntegerCoordinates=f404desc5IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc5IntegerLeftProduct*f404desc5IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc5IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc5IntegerLeftProduct*f404desc5IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc5IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc5IntegerForm=f404desc5Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc5IntegerForm) (f404desc5Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 3
    f409rawInteger f404desc5IntegerCoordinates f404desc5IntegerLeftProduct f404desc5IntegerForm
    f409rawM4Form f404desc5 f404desc5Form f409_raw_integer_check hD hV hY hF

theorem f404desc5_source_form (x y : Fin 2 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5] (natFourWordBlock f404basis (complexify b404relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
          (natFourWordBlock f404basis (complexify b404relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f404desc5Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 5
    f404basis b404relative
    f409basis f404desc5 f409rawM4Form f404desc5Form
    f404desc5_actual f409_actual_raw_M4_matrix f404desc5_compression_check x y


#print axioms f404desc5_compression_check
#print axioms f404desc5_source_form
end TorusLean.BosonFiniteCertificate
