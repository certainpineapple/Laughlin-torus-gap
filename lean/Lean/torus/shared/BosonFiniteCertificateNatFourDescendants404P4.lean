import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates404
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger408
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

def f404desc4Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(204175759096392037358205023/5859375000000000000000), (-194066575560429469008589/4687500000000000000000);
    (-194066575560429469008589/4687500000000000000000), (5227860887353880183729773/468750000000000000000)]

private def f404desc4IntegerCoordinates : Matrix (Fin 15) (Fin 2) ℤ :=
  !![1, (-1);
    8, (-8);
    8, (-2);
    8, 16;
    5, 13;
    4, (-10);
    (-24), 12;
    0, 24;
    0, (-42);
    40, (-100);
    (-24), 12;
    (-84), 66;
    (-8), 20;
    48, 0;
    18, 0]

private def f404desc4IntegerLeftProduct : Matrix (Fin 2) (Fin 15) ℤ :=
  !![(-5672083052161476429310414080), (-1831935816841607553258355008), (-1354823264685473293911107904), 5037436754734840089267362784, 5290345359334810821196635648, (-692536225263906442849912704), (-936316853408064290081473920), 652850158409421693460210368, (-400351715350073519699570688), 1109077132200392036797696512, (-1681251849219265766098243776), (-1180880298818821108532167296), 403239879299489724529656576, 1208914200886180654264047552, 1089911326830322999710357504;
    9247969980958826746513054080, 588684794046928016104121088, 128170949947513175840598720, 631776988987210158711578976, 5116008393602329991035892736, (-432407189894738170578608256), (-676047572459273298762835008), (-437007897087809051506001184), 369946789061998758945458688, (-1287538235541907830170631360), (-824025841651816083472207680), (-239950909283853506453582592), (-1762106073528063563322598464), (-1122882280319900355551091360), (-506370050445754297453893120)]

private def f404desc4IntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![313613965972058169382202915328, (-372607825076024580496490880);
    (-372607825076024580496490880), 100374929037194499527611641600]

theorem f404desc4_compression_check :
    f404desc4ᵀ*f408rawM4Form*f404desc4=f404desc4Form := by
  have hD : natFourIntegerMatrix 3 f404desc4IntegerCoordinates=f404desc4 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 3 f404desc4IntegerCoordinates) (f404desc4) (by decide +kernel) a b
  have hV : f404desc4IntegerCoordinatesᵀ*f408rawInteger=f404desc4IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 15) => (f404desc4IntegerCoordinatesᵀ*f408rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 15) => (f404desc4IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 15) => (f404desc4IntegerCoordinatesᵀ*f408rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 15) => (f404desc4IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f404desc4IntegerLeftProduct*f404desc4IntegerCoordinates=f404desc4IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc4IntegerLeftProduct*f404desc4IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc4IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc4IntegerLeftProduct*f404desc4IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc4IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc4IntegerForm=f404desc4Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc4IntegerForm) (f404desc4Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 3
    f408rawInteger f404desc4IntegerCoordinates f404desc4IntegerLeftProduct f404desc4IntegerForm
    f408rawM4Form f404desc4 f404desc4Form f408_raw_integer_check hD hV hY hF

theorem f404desc4_source_form (x y : Fin 2 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4] (natFourWordBlock f404basis (complexify b404relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
          (natFourWordBlock f404basis (complexify b404relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f404desc4Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 4
    f404basis b404relative
    f408basis f404desc4 f408rawM4Form f404desc4Form
    f404desc4_actual f408_actual_raw_M4_matrix f404desc4_compression_check x y


#print axioms f404desc4_compression_check
#print axioms f404desc4_source_form
end TorusLean.BosonFiniteCertificate
