import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates400
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger409
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

def f400desc9Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(333868487902019768316747106998369/244140625000000000000)]

private def f400desc9IntegerCoordinates : Matrix (Fin 18) (Fin 1) ℤ :=
  !![4;
    108;
    432;
    1008;
    1512;
    864;
    6048;
    12096;
    7560;
    9072;
    30240;
    6720;
    2016;
    18144;
    30240;
    45360;
    60480;
    30240]

private def f400desc9IntegerLeftProduct : Matrix (Fin 1) (Fin 18) ℤ :=
  !![0, 1008686490963586577804110417920, 6607547065108440380112554472192, 9300980427686081008868918292480, 7842047101114094602499356733952, 328199276524885219129593012480, 1831169064283047101508628220928, 6526637079204053389912844275584, 9947715386437816034165104764672, 1782920028890277022890213509760, 8625208802562018686737566162432, 8533056433065478887790986789888, 299345205615001989879406625280, 1376342551759271376439548790272, 8625782814118040218431319941888, 4929315590965182617773168390656, 4731360166175627460681966797568, 1564514745617929868156904314112]

private def f400desc9IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![1367525326446672971025396150265319424]

theorem f400desc9_compression_check :
    f400desc9ᵀ*f409rawM4Form*f400desc9=f400desc9Form := by
  have hD : natFourIntegerMatrix 1 f400desc9IntegerCoordinates=f400desc9 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f400desc9IntegerCoordinates) (f400desc9) (by decide +kernel) a b
  have hV : f400desc9IntegerCoordinatesᵀ*f409rawInteger=f400desc9IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 18) => (f400desc9IntegerCoordinatesᵀ*f409rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 18) => (f400desc9IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f400desc9IntegerLeftProduct*f400desc9IntegerCoordinates=f400desc9IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc9IntegerLeftProduct*f400desc9IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc9IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc9IntegerForm=f400desc9Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc9IntegerForm) (f400desc9Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f409rawInteger f400desc9IntegerCoordinates f400desc9IntegerLeftProduct f400desc9IntegerForm
    f409rawM4Form f400desc9 f400desc9Form f409_raw_integer_check hD hV hY hF

theorem f400desc9_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[9] (natFourWordBlock f400basis (complexify b400relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[9]
          (natFourWordBlock f400basis (complexify b400relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f400desc9Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 9
    f400basis b400relative
    f409basis f400desc9 f409rawM4Form f400desc9Form
    f400desc9_actual f409_actual_raw_M4_matrix f400desc9_compression_check x y


#print axioms f400desc9_compression_check
#print axioms f400desc9_source_form
end TorusLean.BosonFiniteCertificate
