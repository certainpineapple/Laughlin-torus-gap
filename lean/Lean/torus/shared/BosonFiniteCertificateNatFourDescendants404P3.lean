import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates404
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger407
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
import torus.shared.BosonFiniteCertificate404

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

def f404desc3Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(355478681884062997958416271/187500000000000000000000), (101861146159362821497887307/187500000000000000000000);
    (101861146159362821497887307/187500000000000000000000), (-136040372339483592799053469/187500000000000000000000)]

private def f404desc3IntegerCoordinates : Matrix (Fin 11) (Fin 2) ℤ :=
  !![1, (-1);
    5, (-5);
    3, 3;
    5, 13;
    (-6), 0;
    (-18), 6;
    4, (-4);
    18, (-48);
    (-18), 12;
    (-12), 24;
    18, 0]

private def f404desc3IntegerLeftProduct : Matrix (Fin 2) (Fin 11) ℤ :=
  !![(-4317602058696462911818282368), (-794945435426871127295002536), (-277721551387648823953425024), 1069736753203949814018024168, (-252172943738481268184959296), (-9593843341260360259462032), 316608723692360474263613184, 308742280652118364644825240, (-266821554604567114678808664), 119544946820986946289158208, 497889746905418254937632968;
    4796257525582605157306736064, 512424765683167435225297320, (-117543077654620838061570240), (-122107168120853580114624264), 28446804514491200406505440, (-194483160816195728427902064), (-334303043058538061979142272), (-209689491262559348662854552), (-169723360427813399868348888), (-226260940106994869999687760), (-305245893689435083878810360)]

private def f404desc3IntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![17062976730435023902003981008, 4889335015649415431898590736;
    4889335015649415431898590736, (-6529937872295212454354566512)]

theorem f404desc3_compression_check :
    f404desc3ᵀ*f407rawM4Form*f404desc3=f404desc3Form := by
  have hD : natFourIntegerMatrix 3 f404desc3IntegerCoordinates=f404desc3 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 3 f404desc3IntegerCoordinates) (f404desc3) (by decide +kernel) a b
  have hV : f404desc3IntegerCoordinatesᵀ*f407rawInteger=f404desc3IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 11) => (f404desc3IntegerCoordinatesᵀ*f407rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 11) => (f404desc3IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 11) => (f404desc3IntegerCoordinatesᵀ*f407rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 11) => (f404desc3IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f404desc3IntegerLeftProduct*f404desc3IntegerCoordinates=f404desc3IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc3IntegerLeftProduct*f404desc3IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc3IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc3IntegerLeftProduct*f404desc3IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc3IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc3IntegerForm=f404desc3Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc3IntegerForm) (f404desc3Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 3
    f407rawInteger f404desc3IntegerCoordinates f404desc3IntegerLeftProduct f404desc3IntegerForm
    f407rawM4Form f404desc3 f404desc3Form f407_raw_integer_check hD hV hY hF

theorem f404desc3_source_form (x y : Fin 2 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3] (natFourWordBlock f404basis (complexify b404relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
          (natFourWordBlock f404basis (complexify b404relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f404desc3Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 3
    f404basis b404relative
    f407basis f404desc3 f407rawM4Form f404desc3Form
    f404desc3_actual f407_actual_raw_M4_matrix f404desc3_compression_check x y


#print axioms f404desc3_compression_check
#print axioms f404desc3_source_form
end TorusLean.BosonFiniteCertificate
