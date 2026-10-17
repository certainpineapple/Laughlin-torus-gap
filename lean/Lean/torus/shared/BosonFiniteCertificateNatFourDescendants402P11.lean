import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates402
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger413
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

def f402desc11Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(13841351401148103603052714882131/1562500000000000000)]

private def f402desc11IntegerCoordinates : Matrix (Fin 39) (Fin 1) ℤ :=
  !![(-1);
    (-31);
    (-146);
    (-418);
    (-825);
    (-1221);
    (-1452);
    (-284);
    (-2332);
    (-5720);
    (-9570);
    (-12144);
    (-6468);
    (-4070);
    (-16500);
    (-22440);
    (-24024);
    (-13200);
    (-27720);
    (-12936);
    (-11550);
    (-748);
    (-7700);
    (-15180);
    (-19800);
    (-20328);
    (-20790);
    (-58080);
    (-46200);
    (-16632);
    (-18480);
    18480;
    11550;
    (-11880);
    (-9240);
    41580;
    92400;
    161700;
    92400]

private def f402desc11IntegerLeftProduct : Matrix (Fin 1) (Fin 39) ℤ :=
  !![0, 0, 0, 0, 0, (-68394171878382650164246423641600), (-1460309331525166224013083373555200), 0, 0, 0, (-3391230789363334834110387916800), (-135000820701353117252842225804800), (-424501121567632069569971017497600), 0, 602758914589278384948193075200, (-23279117749568123842639401638400), (-113717554489449615523008680582400), 18697577514603554068960310899200, 5404416799058431019494330521600, 23575314104722675057067311564800, (-38137098173857835839236507513600), 0, 0, (-1721331976529325443584354099200), (-24436488439102134220225584307200), (-65803925348181503608139332243200), (-112959788575285710622171238400), 9368600748688700465021996659200, 21379547221150785777832122086400, 20219320359966929741978126515200, 4181044847440000311084544704000, (-8233740688635251785848623443200), 0, 1196994672307857238669865088000, (-11481223852631335119568052313600), (-26187967580117546169272175724800), 5393386777482910541660300870400, 0, 0]

private def f402desc11IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![8858464896734786305953737524563840000]

theorem f402desc11_compression_check :
    f402desc11ᵀ*f413rawM4Form*f402desc11=f402desc11Form := by
  have hD : natFourIntegerMatrix 1 f402desc11IntegerCoordinates=f402desc11 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f402desc11IntegerCoordinates) (f402desc11) (by decide +kernel) a b
  have hV : f402desc11IntegerCoordinatesᵀ*f413rawInteger=f402desc11IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 39) => (f402desc11IntegerCoordinatesᵀ*f413rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 39) => (f402desc11IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f402desc11IntegerLeftProduct*f402desc11IntegerCoordinates=f402desc11IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc11IntegerLeftProduct*f402desc11IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc11IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc11IntegerForm=f402desc11Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc11IntegerForm) (f402desc11Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f413rawInteger f402desc11IntegerCoordinates f402desc11IntegerLeftProduct f402desc11IntegerForm
    f413rawM4Form f402desc11 f402desc11Form f413_raw_integer_check hD hV hY hF

theorem f402desc11_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[11] (natFourWordBlock f402basis (complexify b402relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[11]
          (natFourWordBlock f402basis (complexify b402relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f402desc11Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 11
    f402basis b402relative
    f413basis f402desc11 f413rawM4Form f402desc11Form
    f402desc11_actual f413_actual_raw_M4_matrix f402desc11_compression_check x y


#print axioms f402desc11_compression_check
#print axioms f402desc11_source_form
end TorusLean.BosonFiniteCertificate
