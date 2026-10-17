import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates405
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger412
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

def f405desc7Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(674171261052147023810193803/12207031250000000000)]

private def f405desc7IntegerCoordinates : Matrix (Fin 34) (Fin 1) ℤ :=
  !![(-1);
    (-16);
    (-30);
    (-16);
    19;
    32;
    14;
    (-64);
    (-128);
    96;
    192;
    0;
    90;
    640;
    392;
    0;
    448;
    448;
    70;
    (-56);
    0;
    160;
    (-448);
    (-504);
    384;
    0;
    (-2688);
    (-672);
    (-1120);
    168;
    0;
    (-210);
    2240;
    560]

private def f405desc7IntegerLeftProduct : Matrix (Fin 1) (Fin 34) ℤ :=
  !![0, 0, 0, 0, (-4353655533794197815813847511040), 3597842140331587727210883901440, (-442082458504067552276481423360), 0, 0, (-27018392795134290350950625280), 262204855362289112276769615360, 35868312847865257216305696000, (-42877529010119018126493388800), (-73723305343012168593110538240), (-370801816164900296453094981120), (-361788731540892850364283271680), (-213328141851584163557902970880), (-502220885600160436357489800960), (-675942733811298769869192744960), 0, (-1919243678683120390935613440), (-158253337237801379557507130880), (-367890906204208947069833771520), (-628437614890304522561405713920), (-20635576739634646243072926720), (-212341991556385745631191946240), (-613835519371664381322421063680), (-185154599217618976932340450560), (-120022933112563478075576340480), (-136761587494946074849969290240), (-105459897803872621211705410560), (-391003047587517611725132185600), 27786147764270176309715066880, 0]

private def f405desc7IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![1988211949394107830859118748303360]

theorem f405desc7_compression_check :
    f405desc7ᵀ*f412rawM4Form*f405desc7=f405desc7Form := by
  have hD : natFourIntegerMatrix 6 f405desc7IntegerCoordinates=f405desc7 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 6 f405desc7IntegerCoordinates) (f405desc7) (by decide +kernel) a b
  have hV : f405desc7IntegerCoordinatesᵀ*f412rawInteger=f405desc7IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 34) => (f405desc7IntegerCoordinatesᵀ*f412rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 34) => (f405desc7IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f405desc7IntegerLeftProduct*f405desc7IntegerCoordinates=f405desc7IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f405desc7IntegerLeftProduct*f405desc7IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f405desc7IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (6*1000000000000000000000000*6) f405desc7IntegerForm=f405desc7Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (6*1000000000000000000000000*6) f405desc7IntegerForm) (f405desc7Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 6
    f412rawInteger f405desc7IntegerCoordinates f405desc7IntegerLeftProduct f405desc7IntegerForm
    f412rawM4Form f405desc7 f405desc7Form f412_raw_integer_check hD hV hY hF

theorem f405desc7_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7] (natFourWordBlock f405basis (complexify b405relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7]
          (natFourWordBlock f405basis (complexify b405relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f405desc7Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 7
    f405basis b405relative
    f412basis f405desc7 f412rawM4Form f405desc7Form
    f405desc7_actual f412_actual_raw_M4_matrix f405desc7_compression_check x y


#print axioms f405desc7_compression_check
#print axioms f405desc7_source_form
end TorusLean.BosonFiniteCertificate
