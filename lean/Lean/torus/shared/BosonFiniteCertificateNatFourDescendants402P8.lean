import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates402
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger410
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

def f402desc8Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(7417195449579658329438718278531/1953125000000000000000)]

private def f402desc8IntegerCoordinates : Matrix (Fin 23) (Fin 1) ℤ :=
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

private def f402desc8IntegerLeftProduct : Matrix (Fin 1) (Fin 23) ℤ :=
  !![0, 0, (-995440447066936532799077095680), (-519781269925811438358468310656), (-1655872015511038754465519098752), (-3758558251656160744425741815040), (-6589339798167384971319613440), (-254524776299302649569673166720), (-241465442577317199200621543040), (-1105481418808632408191895162816), (-218609704439383345236225569280), (-334234825357885570512140981184), (-665812735102331773849879284480), (-307818047137242977411160932352), (-77318766684145012737608835840), (-94756582778134267582528838400), (-343476852610126123695500582400), (-393179062282031476538751144960), (-212305032465871118995622983680), (-93692768189280949020786693888), (-42101467246942204184885813760), (-120356406435504064756594625280), 85519075800236573201288241408]

private def f402desc8IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![3797604070184785064672623758607872]

theorem f402desc8_compression_check :
    f402desc8ᵀ*f410rawM4Form*f402desc8=f402desc8Form := by
  have hD : natFourIntegerMatrix 1 f402desc8IntegerCoordinates=f402desc8 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f402desc8IntegerCoordinates) (f402desc8) (by decide +kernel) a b
  have hV : f402desc8IntegerCoordinatesᵀ*f410rawInteger=f402desc8IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f402desc8IntegerCoordinatesᵀ*f410rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f402desc8IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f402desc8IntegerLeftProduct*f402desc8IntegerCoordinates=f402desc8IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc8IntegerLeftProduct*f402desc8IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc8IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc8IntegerForm=f402desc8Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc8IntegerForm) (f402desc8Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f410rawInteger f402desc8IntegerCoordinates f402desc8IntegerLeftProduct f402desc8IntegerForm
    f410rawM4Form f402desc8 f402desc8Form f410_raw_integer_check hD hV hY hF

theorem f402desc8_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8] (natFourWordBlock f402basis (complexify b402relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8]
          (natFourWordBlock f402basis (complexify b402relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f402desc8Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 8
    f402basis b402relative
    f410basis f402desc8 f410rawM4Form f402desc8Form
    f402desc8_actual f410_actual_raw_M4_matrix f402desc8_compression_check x y


#print axioms f402desc8_compression_check
#print axioms f402desc8_source_form
end TorusLean.BosonFiniteCertificate
