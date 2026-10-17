import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates405
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger409
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

def f405desc4Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1527550110668660889248185799/46875000000000000000000)]

private def f405desc4IntegerCoordinates : Matrix (Fin 18) (Fin 1) ℤ :=
  !![(-1);
    (-7);
    0;
    8;
    2;
    (-4);
    40;
    8;
    (-26);
    36;
    16;
    8;
    4;
    (-12);
    (-124);
    (-36);
    (-8);
    96]

private def f405desc4IntegerLeftProduct : Matrix (Fin 1) (Fin 18) ℤ :=
  !![0, (-1318104044978241098764930560), 2161726135602845939878939200, (-8588256156350512819275657024), 649472168688869956973902080, 2131229339868604950094987200, 6237639295521329937769910400, (-6305087051777559248831206560), (-8019692978621867957969379264), (-1134580861961873314836267552), (-5782467911267477449657139328), (-5939872904687741692481189376), 2632796045137585323831628800, (-4447719487061469287683550592), (-6089366760920386650462221568), (-3594026246775944577634904448), (-3168384271022569209036847680), 410968244975644827718879104]

private def f405desc4IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![1173158484993531562942606693632]

theorem f405desc4_compression_check :
    f405desc4ᵀ*f409rawM4Form*f405desc4=f405desc4Form := by
  have hD : natFourIntegerMatrix 6 f405desc4IntegerCoordinates=f405desc4 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 6 f405desc4IntegerCoordinates) (f405desc4) (by decide +kernel) a b
  have hV : f405desc4IntegerCoordinatesᵀ*f409rawInteger=f405desc4IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 18) => (f405desc4IntegerCoordinatesᵀ*f409rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 18) => (f405desc4IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f405desc4IntegerLeftProduct*f405desc4IntegerCoordinates=f405desc4IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f405desc4IntegerLeftProduct*f405desc4IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f405desc4IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (6*1000000000000000000000000*6) f405desc4IntegerForm=f405desc4Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (6*1000000000000000000000000*6) f405desc4IntegerForm) (f405desc4Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 6
    f409rawInteger f405desc4IntegerCoordinates f405desc4IntegerLeftProduct f405desc4IntegerForm
    f409rawM4Form f405desc4 f405desc4Form f409_raw_integer_check hD hV hY hF

theorem f405desc4_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4] (natFourWordBlock f405basis (complexify b405relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
          (natFourWordBlock f405basis (complexify b405relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f405desc4Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 4
    f405basis b405relative
    f409basis f405desc4 f409rawM4Form f405desc4Form
    f405desc4_actual f409_actual_raw_M4_matrix f405desc4_compression_check x y


#print axioms f405desc4_compression_check
#print axioms f405desc4_source_form
end TorusLean.BosonFiniteCertificate
