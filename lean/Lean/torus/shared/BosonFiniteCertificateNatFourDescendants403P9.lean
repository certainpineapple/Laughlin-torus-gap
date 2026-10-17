import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates403
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger412
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

def f403desc9Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(813315233294021972317909326957/12207031250000000000)]

private def f403desc9IntegerCoordinates : Matrix (Fin 34) (Fin 1) ℤ :=
  !![1;
    24;
    78;
    120;
    45;
    (-144);
    (-126);
    168;
    912;
    1008;
    (-288);
    (-2016);
    918;
    576;
    (-3528);
    (-3024);
    (-2016);
    (-10080);
    (-2310);
    344;
    2376;
    2016;
    (-1008);
    (-1512);
    4320;
    4032;
    (-6048);
    (-2016);
    (-5040);
    2520;
    6048;
    1890;
    10080;
    1680]

private def f403desc9IntegerLeftProduct : Matrix (Fin 1) (Fin 34) ℤ :=
  !![0, 0, 0, 0, (-34766585813300027611768612024320), (-42731060935566757120334434990080), (-91663414296746586007251276564480), 0, 0, (-5564086086484001653862584320), (-6419043417735390761422344138240), (-29233221700306963132578629664000), (-8830069784711407831845335040), 80574971764374506831103498240, (-8072385966102918008832773644800), (-13630005649504647548728702133760), (-2004795691424529293864917463040), (-5481645920632313376221487663360), (-6501404775585469215683694182400), 0, (-395243818701919229432033280), (-579314007939871277322051156480), (-5614575502374321003609887393280), (-11273361251780630656854732096000), 539763178360854474211467985920, (-655408972205988236474977520640), (-4429083526348518621426894336000), (-958600811481757755242805123840), (-880348444611054107232078950400), (-905943201700893187051681367040), (-826580682150459956409476090880), (-3111687342460379081696005324800), 428896965568951300739576647680, 0]

private def f403desc9IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![266507135645785119889132528257269760]

theorem f403desc9_compression_check :
    f403desc9ᵀ*f412rawM4Form*f403desc9=f403desc9Form := by
  have hD : natFourIntegerMatrix 2 f403desc9IntegerCoordinates=f403desc9 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 2 f403desc9IntegerCoordinates) (f403desc9) (by decide +kernel) a b
  have hV : f403desc9IntegerCoordinatesᵀ*f412rawInteger=f403desc9IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f403desc9IntegerCoordinatesᵀ*f412rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f403desc9IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f403desc9IntegerLeftProduct*f403desc9IntegerCoordinates=f403desc9IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc9IntegerLeftProduct*f403desc9IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc9IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc9IntegerForm=f403desc9Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc9IntegerForm) (f403desc9Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 2
    f412rawInteger f403desc9IntegerCoordinates f403desc9IntegerLeftProduct f403desc9IntegerForm
    f412rawM4Form f403desc9 f403desc9Form f412_raw_integer_check hD hV hY hF

theorem f403desc9_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[9] (natFourWordBlock f403basis (complexify b403relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[9]
          (natFourWordBlock f403basis (complexify b403relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f403desc9Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 9
    f403basis b403relative
    f412basis f403desc9 f412rawM4Form f403desc9Form
    f403desc9_actual f412_actual_raw_M4_matrix f403desc9_compression_check x y


#print axioms f403desc9_compression_check
#print axioms f403desc9_source_form
end TorusLean.BosonFiniteCertificate
