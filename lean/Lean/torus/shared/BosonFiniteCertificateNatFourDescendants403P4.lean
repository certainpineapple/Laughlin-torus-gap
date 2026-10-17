import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates403
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger407
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

def f403desc4Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(5230437302483844371577264861/250000000000000000000000)]

private def f403desc4IntegerCoordinates : Matrix (Fin 11) (Fin 1) ℤ :=
  !![1;
    9;
    3;
    (-15);
    18;
    (-18);
    (-36);
    (-42);
    14;
    36;
    30]

private def f403desc4IntegerLeftProduct : Matrix (Fin 1) (Fin 11) ℤ :=
  !![(-7243977383895277939625682048), (-388910112002524736630604648), (-296582636984161693818455424), (-1916917318090559011898628504), 331409906319281864468479488, (-377015148359216663919753552), (-1114542634299404461099427520), (-641387869510906828544981256), 331284778289283410743860936, (-178091710694682105214097088), (-382433609274580748488335192)]

private def f403desc4IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![83686996839741509945236237776]

theorem f403desc4_compression_check :
    f403desc4ᵀ*f407rawM4Form*f403desc4=f403desc4Form := by
  have hD : natFourIntegerMatrix 2 f403desc4IntegerCoordinates=f403desc4 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 2 f403desc4IntegerCoordinates) (f403desc4) (by decide +kernel) a b
  have hV : f403desc4IntegerCoordinatesᵀ*f407rawInteger=f403desc4IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 11) => (f403desc4IntegerCoordinatesᵀ*f407rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 11) => (f403desc4IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f403desc4IntegerLeftProduct*f403desc4IntegerCoordinates=f403desc4IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc4IntegerLeftProduct*f403desc4IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc4IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc4IntegerForm=f403desc4Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc4IntegerForm) (f403desc4Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 2
    f407rawInteger f403desc4IntegerCoordinates f403desc4IntegerLeftProduct f403desc4IntegerForm
    f407rawM4Form f403desc4 f403desc4Form f407_raw_integer_check hD hV hY hF

theorem f403desc4_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4] (natFourWordBlock f403basis (complexify b403relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
          (natFourWordBlock f403basis (complexify b403relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f403desc4Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 4
    f403basis b403relative
    f407basis f403desc4 f407rawM4Form f403desc4Form
    f403desc4_actual f407_actual_raw_M4_matrix f403desc4_compression_check x y


#print axioms f403desc4_compression_check
#print axioms f403desc4_source_form
end TorusLean.BosonFiniteCertificate
