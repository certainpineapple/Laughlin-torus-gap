import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates403
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger410
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

def f403desc7Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(2457345699242439080360850865251/7812500000000000000000)]

private def f403desc7IntegerCoordinates : Matrix (Fin 23) (Fin 1) ℤ :=
  !![1;
    18;
    39;
    24;
    (-42);
    (-42);
    90;
    288;
    0;
    (-504);
    84;
    (-672);
    (-630);
    (-840);
    128;
    504;
    0;
    (-210);
    504;
    0;
    0;
    420;
    840]

private def f403desc7IntegerLeftProduct : Matrix (Fin 1) (Fin 23) ℤ :=
  !![0, 0, 191204479837619632568232357120, (-583157209020973771102193874816), (-977852759101798886044337766528), (-1871970190642935685313215384320), 3123481835060240168142673920, 128565977543691788688744078720, (-131781349456124890815618963840), (-792120931873769294348968531008), 105131030402027715625127600640, (-253439508044507600184001556544), (-416802174704992494567662688000), (-267875166682440303995233142784), 29954977637504423854372565760, 69849388134472658801151179520, (-236922555644475295896580999680), (-336402003867702264922857937920), (-85811446024259557562010040320), (-150587362000658471329126285056), (-69908882142810050890902374400), (-59020455792276306687014924544), 97752959385502859208223488]

private def f403desc7IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![1258160998012128809144755643008512]

theorem f403desc7_compression_check :
    f403desc7ᵀ*f410rawM4Form*f403desc7=f403desc7Form := by
  have hD : natFourIntegerMatrix 2 f403desc7IntegerCoordinates=f403desc7 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 2 f403desc7IntegerCoordinates) (f403desc7) (by decide +kernel) a b
  have hV : f403desc7IntegerCoordinatesᵀ*f410rawInteger=f403desc7IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f403desc7IntegerCoordinatesᵀ*f410rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f403desc7IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f403desc7IntegerLeftProduct*f403desc7IntegerCoordinates=f403desc7IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc7IntegerLeftProduct*f403desc7IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc7IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc7IntegerForm=f403desc7Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc7IntegerForm) (f403desc7Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 2
    f410rawInteger f403desc7IntegerCoordinates f403desc7IntegerLeftProduct f403desc7IntegerForm
    f410rawM4Form f403desc7 f403desc7Form f410_raw_integer_check hD hV hY hF

theorem f403desc7_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7] (natFourWordBlock f403basis (complexify b403relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7]
          (natFourWordBlock f403basis (complexify b403relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f403desc7Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 7
    f403basis b403relative
    f410basis f403desc7 f410rawM4Form f403desc7Form
    f403desc7_actual f410_actual_raw_M4_matrix f403desc7_compression_check x y


#print axioms f403desc7_compression_check
#print axioms f403desc7_source_form
end TorusLean.BosonFiniteCertificate
