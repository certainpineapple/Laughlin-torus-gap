import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates405
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger411
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
import torus.shared.BosonFiniteCertificate405

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

def f405desc6Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(56113814624030709763177964299/7812500000000000000000)]

private def f405desc6IntegerCoordinates : Matrix (Fin 27) (Fin 1) ℤ :=
  !![(-1);
    (-13);
    (-17);
    1;
    18;
    14;
    (-38);
    (-18);
    112;
    44;
    (-36);
    108;
    312;
    36;
    136;
    70;
    (-18);
    72;
    (-24);
    (-468);
    132;
    (-528);
    (-630);
    (-280);
    36;
    420;
    560]

private def f405desc6IntegerLeftProduct : Matrix (Fin 1) (Fin 27) ℤ :=
  !![0, 0, 0, (-272431400694876658848522988800), (-258075627278009477112689701248), 15267905132966834974030183680, 0, (-5904166965061720448747243520), 53176663391707240725499971840, (-178424264011193890194242384640), (-325665518677037791544727665280), 9683962998571863929262545280, (-38725942304731600476951402240), (-268744624508512168125327608256), (-138399835937572308320825927040), (-175792629354575483051231542272), (-3433582432002320374121533440), (-9933345269580572093236711680), (-52310399171760401309530381440), (-284634511826477066705739213504), (-10849059281206033340216215680), (-103075182812835550734316790400), (-182681719326192630502944433152), (-62353204831516900881741408000), (-75593269948307159152917671040), (-48069183089291431933714044672), 15606875560879576066289650560]

private def f405desc6IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![258572457787533510588724059489792]

theorem f405desc6_compression_check :
    f405desc6ᵀ*f411rawM4Form*f405desc6=f405desc6Form := by
  have hD : natFourIntegerMatrix 6 f405desc6IntegerCoordinates=f405desc6 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 6 f405desc6IntegerCoordinates) (f405desc6) (by decide +kernel) a b
  have hV : f405desc6IntegerCoordinatesᵀ*f411rawInteger=f405desc6IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f405desc6IntegerCoordinatesᵀ*f411rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f405desc6IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f405desc6IntegerLeftProduct*f405desc6IntegerCoordinates=f405desc6IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f405desc6IntegerLeftProduct*f405desc6IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f405desc6IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (6*1000000000000000000000000*6) f405desc6IntegerForm=f405desc6Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (6*1000000000000000000000000*6) f405desc6IntegerForm) (f405desc6Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 6
    f411rawInteger f405desc6IntegerCoordinates f405desc6IntegerLeftProduct f405desc6IntegerForm
    f411rawM4Form f405desc6 f405desc6Form f411_raw_integer_check hD hV hY hF

theorem f405desc6_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6] (natFourWordBlock f405basis (complexify b405relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6]
          (natFourWordBlock f405basis (complexify b405relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f405desc6Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 6
    f405basis b405relative
    f411basis f405desc6 f411rawM4Form f405desc6Form
    f405desc6_actual f411_actual_raw_M4_matrix f405desc6_compression_check x y


#print axioms f405desc6_compression_check
#print axioms f405desc6_source_form
end TorusLean.BosonFiniteCertificate
