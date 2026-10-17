import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates400
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger407
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

def f400desc7Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(7160206081267400216654941586181/3906250000000000000000)]

private def f400desc7IntegerCoordinates : Matrix (Fin 11) (Fin 1) ℤ :=
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

private def f400desc7IntegerLeftProduct : Matrix (Fin 1) (Fin 11) ℤ :=
  !![(-33897214615186923963514997760), 29336662390286657312307012960, 73695014566110820233838568448, 49803401412080934165994930848, (-17705433355270454682474670080), 92138280706691552495890980288, 181432795796637583122462827520, 147194082515817766131969589344, 25933590883162166046358782240, 105610192897127754247024007808, 134180472764682059755840792992]

private def f400desc7IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![1833012756804454455463665046062336]

theorem f400desc7_compression_check :
    f400desc7ᵀ*f407rawM4Form*f400desc7=f400desc7Form := by
  have hD : natFourIntegerMatrix 1 f400desc7IntegerCoordinates=f400desc7 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f400desc7IntegerCoordinates) (f400desc7) (by decide +kernel) a b
  have hV : f400desc7IntegerCoordinatesᵀ*f407rawInteger=f400desc7IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 11) => (f400desc7IntegerCoordinatesᵀ*f407rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 11) => (f400desc7IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f400desc7IntegerLeftProduct*f400desc7IntegerCoordinates=f400desc7IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc7IntegerLeftProduct*f400desc7IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc7IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc7IntegerForm=f400desc7Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc7IntegerForm) (f400desc7Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f407rawInteger f400desc7IntegerCoordinates f400desc7IntegerLeftProduct f400desc7IntegerForm
    f407rawM4Form f400desc7 f400desc7Form f407_raw_integer_check hD hV hY hF

theorem f400desc7_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7] (natFourWordBlock f400basis (complexify b400relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7]
          (natFourWordBlock f400basis (complexify b400relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f400desc7Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 7
    f400basis b400relative
    f407basis f400desc7 f407rawM4Form f400desc7Form
    f400desc7_actual f407_actual_raw_M4_matrix f400desc7_compression_check x y


#print axioms f400desc7_compression_check
#print axioms f400desc7_source_form
end TorusLean.BosonFiniteCertificate
