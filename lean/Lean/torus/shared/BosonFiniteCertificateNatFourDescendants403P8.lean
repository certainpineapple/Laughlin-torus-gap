import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates403
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger411
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

def f403desc8Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(48011607971035311756662923221423/7812500000000000000000)]

private def f403desc8IntegerCoordinates : Matrix (Fin 27) (Fin 1) ℤ :=
  !![1;
    21;
    57;
    63;
    (-18);
    (-126);
    126;
    546;
    336;
    (-588);
    (-588);
    372;
    (-504);
    (-2436);
    (-1512);
    (-2310);
    218;
    1176;
    504;
    (-924);
    1596;
    336;
    (-1050);
    (-840);
    924;
    2940;
    1680]

private def f403desc8IntegerLeftProduct : Matrix (Fin 1) (Fin 27) ℤ :=
  !![0, 0, 0, (-3720037877481343933707844458240), (-5212196034106519249112847076992), (-11914644571358846600335797699840), 0, (-25808026149097199116424017920), 108127112715883800139592113920, (-2971442076175197751767900781824), (-8136547308136107632128818165120), 282075141405769198431571912320, (-438434576541111631222396442880), (-3288146570360333849367095916096), (-1259313332734687051405652296320), (-1644140298191141855009551583232), (-15008719182156376988987289600), 40724165427747802246802223360, (-202424484718640425938522963840), (-2751788495764667759111346685248), (-38786413636442247063898400640), (-629409054862382408905496549760), (-1146652034949830322410480188416), (-365344416381343473947149390080), (-440015881148559538690592764800), (-390674968609850987517868458240), 275029232896841646159241280640]

private def f403desc8IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![24581943281170079619411416689368576]

theorem f403desc8_compression_check :
    f403desc8ᵀ*f411rawM4Form*f403desc8=f403desc8Form := by
  have hD : natFourIntegerMatrix 2 f403desc8IntegerCoordinates=f403desc8 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 2 f403desc8IntegerCoordinates) (f403desc8) (by decide +kernel) a b
  have hV : f403desc8IntegerCoordinatesᵀ*f411rawInteger=f403desc8IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f403desc8IntegerCoordinatesᵀ*f411rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f403desc8IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f403desc8IntegerLeftProduct*f403desc8IntegerCoordinates=f403desc8IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc8IntegerLeftProduct*f403desc8IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc8IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc8IntegerForm=f403desc8Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc8IntegerForm) (f403desc8Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 2
    f411rawInteger f403desc8IntegerCoordinates f403desc8IntegerLeftProduct f403desc8IntegerForm
    f411rawM4Form f403desc8 f403desc8Form f411_raw_integer_check hD hV hY hF

theorem f403desc8_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8] (natFourWordBlock f403basis (complexify b403relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[8]
          (natFourWordBlock f403basis (complexify b403relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f403desc8Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 8
    f403basis b403relative
    f411basis f403desc8 f411rawM4Form f403desc8Form
    f403desc8_actual f411_actual_raw_M4_matrix f403desc8_compression_check x y


#print axioms f403desc8_compression_check
#print axioms f403desc8_source_form
end TorusLean.BosonFiniteCertificate
