import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates404
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger406
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

def f404desc2Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(15826030807921670085417523/281250000000000000000000), (11935766896742863630924801/140625000000000000000000);
    (11935766896742863630924801/140625000000000000000000), (-1857311882032018269944807/11250000000000000000000)]

private def f404desc2IntegerCoordinates : Matrix (Fin 9) (Fin 2) ℤ :=
  !![1, (-1);
    2, (-2);
    1, 5;
    2, 4;
    (-10), 4;
    0, (-12);
    6, (-12);
    (-8), 8;
    6, 6]

private def f404desc2IntegerLeftProduct : Matrix (Fin 2) (Fin 9) ℤ :=
  !![(-813675278838235138918451424), (-180364382098734498038509080), 88088827766261112394721392, 127661558850332305449940080, (-35974543875251953646958688), 36641536436990837790281392, 100601715537274452784583856, 3446406991830628364964336, 66940101230125104696142240;
    862903299158981993126015136, 105668882128604330203719000, (-178672772002772475318276496), (-13936671804750967746926640), (-13183304579258753108663936), (-56551173104133146644076416), (-52885861085115765073925520), (-50292833827265233252465536), (-53444402718731296167491104)]

private def f404desc2IntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![506432985853493442733360736, 763889081391543272379187264;
    763889081391543272379187264, (-1485849505625614615955845600)]

theorem f404desc2_compression_check :
    f404desc2ᵀ*f406rawM4Form*f404desc2=f404desc2Form := by
  have hD : natFourIntegerMatrix 3 f404desc2IntegerCoordinates=f404desc2 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 3 f404desc2IntegerCoordinates) (f404desc2) (by decide +kernel) a b
  have hV : f404desc2IntegerCoordinatesᵀ*f406rawInteger=f404desc2IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 9) => (f404desc2IntegerCoordinatesᵀ*f406rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 9) => (f404desc2IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 9) => (f404desc2IntegerCoordinatesᵀ*f406rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 9) => (f404desc2IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f404desc2IntegerLeftProduct*f404desc2IntegerCoordinates=f404desc2IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc2IntegerLeftProduct*f404desc2IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc2IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc2IntegerLeftProduct*f404desc2IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc2IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc2IntegerForm=f404desc2Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc2IntegerForm) (f404desc2Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 3
    f406rawInteger f404desc2IntegerCoordinates f404desc2IntegerLeftProduct f404desc2IntegerForm
    f406rawM4Form f404desc2 f404desc2Form f406_raw_integer_check hD hV hY hF

theorem f404desc2_source_form (x y : Fin 2 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2] (natFourWordBlock f404basis (complexify b404relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
          (natFourWordBlock f404basis (complexify b404relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f404desc2Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 2
    f404basis b404relative
    f406basis f404desc2 f406rawM4Form f404desc2Form
    f404desc2_actual f406_actual_raw_M4_matrix f404desc2_compression_check x y


#print axioms f404desc2_compression_check
#print axioms f404desc2_source_form
end TorusLean.BosonFiniteCertificate
