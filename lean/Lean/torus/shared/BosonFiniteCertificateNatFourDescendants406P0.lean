import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates406
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger406
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
import torus.shared.BosonFiniteCertificate406

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

def f406desc0Form : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(-9199736882925944727397257/125000000000000000000000), (554149950781640854582989/15625000000000000000000), (123306130466991470781063/78125000000000000000000);
    (554149950781640854582989/15625000000000000000000), (-2330763623171824960268487/125000000000000000000000), (-11743066281008038280521229/625000000000000000000000);
    (123306130466991470781063/78125000000000000000000), (-11743066281008038280521229/625000000000000000000000), (-39367563816231960934604689/1875000000000000000000000)]

private def f406desc0IntegerCoordinates : Matrix (Fin 9) (Fin 3) ℤ :=
  !![(-3), 3, 3;
    18, (-18), (-18);
    (-45), 15, 5;
    30, 0, 0;
    0, 30, 40;
    0, (-60), (-20);
    0, 30, 0;
    0, 0, (-40);
    0, 0, 30]

private def f406desc0IntegerLeftProduct : Matrix (Fin 3) (Fin 9) ℤ :=
  !![975327731221986750697143840, (-761902389356210156322767160), 810650853803046204599709744, (-437286364461732658812402384), (-255592722307473503356231008), (-201920049972498549780899712), (-44279105774221026569459088), 298027307467721381881310496, (-38886455218513597720609248);
    (-461471288125476610502275680), 699934485654731906240880120, (-226853961338471698781674704), 257579143287656087832071184, (-80181309203168688996644352), (-65391999338750297456121648), (-30451158160947242194442832), (-24428009433222877566595536), (-29007300925826199270666912);
    (-805052977917733862517143520), 826774393207851250451838200, 316693722102091233746951856, (-54179796464022561122461296), (-52400336721064577211913792), 8706145856001761422800352, (-75631480389879217758163152), (-7740287820034283710057056), (-40742545254867545104340512)]

private def f406desc0IntegerForm : Matrix (Fin 3) (Fin 3) ℤ :=
  !![(-66238105557066802037260250400), 31919037165022513223980166400, 1420486622979741743397845760;
    31919037165022513223980166400, (-16781498086837139713933106400), (-16910015444651575123950569760);
    1420486622979741743397845760, (-16910015444651575123950569760), (-18896430631791341248610250720)]

theorem f406desc0_compression_check :
    f406desc0ᵀ*f406rawM4Form*f406desc0=f406desc0Form := by
  have hD : natFourIntegerMatrix 30 f406desc0IntegerCoordinates=f406desc0 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 30 f406desc0IntegerCoordinates) (f406desc0) (by decide +kernel) a b
  have hV : f406desc0IntegerCoordinatesᵀ*f406rawInteger=f406desc0IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 9) => (f406desc0IntegerCoordinatesᵀ*f406rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 9) => (f406desc0IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 9) => (f406desc0IntegerCoordinatesᵀ*f406rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 9) => (f406desc0IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 9) => (f406desc0IntegerCoordinatesᵀ*f406rawInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 9) => (f406desc0IntegerLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f406desc0IntegerLeftProduct*f406desc0IntegerCoordinates=f406desc0IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc0IntegerLeftProduct*f406desc0IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc0IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc0IntegerLeftProduct*f406desc0IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc0IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc0IntegerLeftProduct*f406desc0IntegerCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc0IntegerForm) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (30*1000000000000000000000000*30) f406desc0IntegerForm=f406desc0Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (30*1000000000000000000000000*30) f406desc0IntegerForm) (f406desc0Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 30
    f406rawInteger f406desc0IntegerCoordinates f406desc0IntegerLeftProduct f406desc0IntegerForm
    f406rawM4Form f406desc0 f406desc0Form f406_raw_integer_check hD hV hY hF

theorem f406desc0_source_form (x y : Fin 3 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0] (natFourWordBlock f406basis (complexify b406relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
          (natFourWordBlock f406basis (complexify b406relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f406desc0Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 0
    f406basis b406relative
    f406basis f406desc0 f406rawM4Form f406desc0Form
    f406desc0_actual f406_actual_raw_M4_matrix f406desc0_compression_check x y


#print axioms f406desc0_compression_check
#print axioms f406desc0_source_form
end TorusLean.BosonFiniteCertificate
