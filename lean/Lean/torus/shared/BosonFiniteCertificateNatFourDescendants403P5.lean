import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates403
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger408
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
import torus.shared.BosonFiniteCertificate403

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

def f403desc5Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(3282176096169977875427019351/7812500000000000000000)]

private def f403desc5IntegerCoordinates : Matrix (Fin 15) (Fin 1) ℤ :=
  !![1;
    12;
    12;
    (-12);
    (-15);
    36;
    24;
    (-120);
    (-60);
    (-120);
    32;
    60;
    0;
    120;
    30]

private def f403desc5IntegerLeftProduct : Matrix (Fin 1) (Fin 15) ℤ :=
  !![(-17249783987304350029163226240), 2770052186283494168684566080, 1544689014397215638295037248, (-8353819446461269594477926624), (-17956541641123537219891252224), 3695496941466146948109085440, 485924976077386062522295872, (-6459936493910569392455529984), (-4242902822099825374404066816), (-3531277652274243406854457344), 1241455173028998101302898880, (-710593142182958264324758272), (-2114331419529264223934766720), (-2359377573288403280991381504), (-1194417718479048418173605376)]

private def f403desc5IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![1680474161239028672218633907712]

theorem f403desc5_compression_check :
    f403desc5ᵀ*f408rawM4Form*f403desc5=f403desc5Form := by
  have hD : natFourIntegerMatrix 2 f403desc5IntegerCoordinates=f403desc5 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 2 f403desc5IntegerCoordinates) (f403desc5) (by decide +kernel) a b
  have hV : f403desc5IntegerCoordinatesᵀ*f408rawInteger=f403desc5IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 15) => (f403desc5IntegerCoordinatesᵀ*f408rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 15) => (f403desc5IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f403desc5IntegerLeftProduct*f403desc5IntegerCoordinates=f403desc5IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc5IntegerLeftProduct*f403desc5IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc5IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc5IntegerForm=f403desc5Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc5IntegerForm) (f403desc5Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 2
    f408rawInteger f403desc5IntegerCoordinates f403desc5IntegerLeftProduct f403desc5IntegerForm
    f408rawM4Form f403desc5 f403desc5Form f408_raw_integer_check hD hV hY hF

theorem f403desc5_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5] (natFourWordBlock f403basis (complexify b403relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
          (natFourWordBlock f403basis (complexify b403relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f403desc5Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 5
    f403basis b403relative
    f408basis f403desc5 f408rawM4Form f403desc5Form
    f403desc5_actual f408_actual_raw_M4_matrix f403desc5_compression_check x y


#print axioms f403desc5_compression_check
#print axioms f403desc5_source_form
end TorusLean.BosonFiniteCertificate
