import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates404
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger411
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

def f404desc7Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(233355110327934306437470089009/1953125000000000000000), (137311867447709167258057710621/1953125000000000000000);
    (137311867447709167258057710621/1953125000000000000000), (44151107805041641518947106939/195312500000000000000)]

private def f404desc7IntegerCoordinates : Matrix (Fin 27) (Fin 2) ℤ :=
  !![1, (-1);
    17, (-17);
    41, (-35);
    59, (-17);
    66, 60;
    70, 140;
    70, (-76);
    210, (-222);
    160, 8;
    140, 448;
    84, 336;
    48, (-126);
    0, (-252);
    252, (-420);
    224, (-812);
    490, (-1330);
    42, (-72);
    (-168), (-48);
    (-504), 504;
    (-420), 924;
    (-1008), 462;
    (-1680), 1008;
    (-210), 210;
    560, (-980);
    (-504), 378;
    840, 210;
    1120, (-280)]

private def f404desc7IntegerLeftProduct : Matrix (Fin 2) (Fin 27) ℤ :=
  !![0, 0, 0, 191665016777751296427807264000, 1596569016699370695579888253824, 2876578733971764508418556238080, 0, (-16317838893265907527797442560), (-113131648255183193119492028160), 457308210039581530421383594752, 801542730536202083138952658560, (-21159368941356492965774732160), (-53941162321375655630037753600), 95743676196387340143966212544, (-192877083701339914475193283200), 68453689084379192412938389248, (-9489678397910625505938923520), (-15128619846330579866644389120), (-85913853439876387848031466880), 8283435712959413619396370368, (-76514546550963157703001233280), (-252419919141411427336982928000), 54742407581478342492794649600, (-21574702256562641029239394560), (-248275108442580494706936927360), 3571896003111138800532736512, (-12255800762698139282790994560);
    0, 0, 0, 1225544915761645036500537154560, 1954302269175422154381613288320, 5573893045980587823095806287360, 0, 1723424929020450668788715520, 141304847506641343442567301120, 855069830218649507734911967488, 2206391047876474844438496908160, (-209103572998899389470415495040), 66853016553424621851982425600, 571532730642362292599005498944, 186273673994606135241962401920, 179877131672417674521142566528, 1002262072874155415191296000, (-52225635317752479035883386880), 53646332334282929683879205760, 409064780630842283969756074944, (-56277146139053431546184768640), 159699679550800374298793448960, (-24933407105987721328040054784), 1053429053979026767791640320, 203016898280371947988107421440, 65611737892090588439581213824, (-96093253496495382158366254080)]

private def f404desc7IntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1075300348391121284063862170153472, 632733085199043842725129930541568;
    632733085199043842725129930541568, 2034483047656318841193082687749120]

theorem f404desc7_compression_check :
    f404desc7ᵀ*f411rawM4Form*f404desc7=f404desc7Form := by
  have hD : natFourIntegerMatrix 3 f404desc7IntegerCoordinates=f404desc7 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 3 f404desc7IntegerCoordinates) (f404desc7) (by decide +kernel) a b
  have hV : f404desc7IntegerCoordinatesᵀ*f411rawInteger=f404desc7IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f404desc7IntegerCoordinatesᵀ*f411rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f404desc7IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f404desc7IntegerCoordinatesᵀ*f411rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f404desc7IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f404desc7IntegerLeftProduct*f404desc7IntegerCoordinates=f404desc7IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc7IntegerLeftProduct*f404desc7IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc7IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc7IntegerLeftProduct*f404desc7IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc7IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc7IntegerForm=f404desc7Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc7IntegerForm) (f404desc7Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 3
    f411rawInteger f404desc7IntegerCoordinates f404desc7IntegerLeftProduct f404desc7IntegerForm
    f411rawM4Form f404desc7 f404desc7Form f411_raw_integer_check hD hV hY hF

theorem f404desc7_source_form (x y : Fin 2 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7] (natFourWordBlock f404basis (complexify b404relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[7]
          (natFourWordBlock f404basis (complexify b404relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f404desc7Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 7
    f404basis b404relative
    f411basis f404desc7 f411rawM4Form f404desc7Form
    f404desc7_actual f411_actual_raw_M4_matrix f404desc7_compression_check x y


#print axioms f404desc7_compression_check
#print axioms f404desc7_source_form
end TorusLean.BosonFiniteCertificate
