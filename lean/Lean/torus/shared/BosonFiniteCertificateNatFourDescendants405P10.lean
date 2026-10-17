import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates405
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger415
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

def f405desc10Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(886488404926848500212229339217/156250000000000000000)]

private def f405desc10IntegerCoordinates : Matrix (Fin 54) (Fin 1) ℤ :=
  !![(-1);
    (-25);
    (-87);
    (-157);
    (-135);
    11;
    165;
    231;
    (-178);
    (-998);
    (-1256);
    (-290);
    1060;
    1338;
    552;
    (-954);
    (-404);
    3510;
    5022;
    3144;
    2780;
    11610;
    10032;
    3444;
    7530;
    11340;
    1764;
    (-350);
    (-2220);
    (-1548);
    650;
    (-126);
    (-3720);
    (-2454);
    4360;
    7110;
    (-14256);
    (-15540);
    8700;
    2160;
    (-35952);
    (-13650);
    (-23940);
    870;
    11070;
    (-2340);
    (-32508);
    12720;
    (-17640);
    (-25704);
    (-5670);
    8400;
    47880;
    34650]

private def f405desc10IntegerLeftProduct : Matrix (Fin 1) (Fin 54) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, 438496387054307922502147470105600, 0, 0, 0, 0, 0, 6665167228614385403705554944000, 141726565609042513824925798348800, 0, 0, 0, (-915653021477338092251210342400), 17899583340957694417212125875200, 0, 118211120633519677216618905600, (-4052582048348667679571534592000), 0, 3739579996741867495872171417600, 0, 0, 0, 0, 0, 0, (-1132626217557333673736471347200), 15636782340895735897042467456000, 0, 0, 412812396342566083571200819200, (-3828780732730291131515715302400), 0, (-483110382254561716098615091200), 168191822734501701801601152000, 0, 0, 0, 0, 28464089534480271741227827200, 2654794138414836770027078860800, 0, (-1140395351210905572099310694400), 0, 0, 0, 0, 0, 0]

private def f405desc10IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![204246928495145894448897639755596800]

private theorem f405desc10_coordinates_decode : natFourIntegerMatrix 6 f405desc10IntegerCoordinates=f405desc10 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 6 f405desc10IntegerCoordinates) (f405desc10) (by decide +kernel) a b

#print axioms f405desc10_coordinates_decode

private theorem f405desc10_left_row0_columns0 :
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 0=f405desc10IntegerLeftProduct 0 0) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 1=f405desc10IntegerLeftProduct 0 1) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 2=f405desc10IntegerLeftProduct 0 2) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 3=f405desc10IntegerLeftProduct 0 3) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 4=f405desc10IntegerLeftProduct 0 4) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 5=f405desc10IntegerLeftProduct 0 5) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 6=f405desc10IntegerLeftProduct 0 6) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 7=f405desc10IntegerLeftProduct 0 7) := by
  decide +kernel

#print axioms f405desc10_left_row0_columns0

private theorem f405desc10_left_row0_columns1 :
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 8=f405desc10IntegerLeftProduct 0 8) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 9=f405desc10IntegerLeftProduct 0 9) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 10=f405desc10IntegerLeftProduct 0 10) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 11=f405desc10IntegerLeftProduct 0 11) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 12=f405desc10IntegerLeftProduct 0 12) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 13=f405desc10IntegerLeftProduct 0 13) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 14=f405desc10IntegerLeftProduct 0 14) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 15=f405desc10IntegerLeftProduct 0 15) := by
  decide +kernel

#print axioms f405desc10_left_row0_columns1

private theorem f405desc10_left_row0_columns2 :
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 16=f405desc10IntegerLeftProduct 0 16) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 17=f405desc10IntegerLeftProduct 0 17) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 18=f405desc10IntegerLeftProduct 0 18) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 19=f405desc10IntegerLeftProduct 0 19) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 20=f405desc10IntegerLeftProduct 0 20) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 21=f405desc10IntegerLeftProduct 0 21) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 22=f405desc10IntegerLeftProduct 0 22) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 23=f405desc10IntegerLeftProduct 0 23) := by
  decide +kernel

#print axioms f405desc10_left_row0_columns2

private theorem f405desc10_left_row0_columns3 :
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 24=f405desc10IntegerLeftProduct 0 24) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 25=f405desc10IntegerLeftProduct 0 25) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 26=f405desc10IntegerLeftProduct 0 26) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 27=f405desc10IntegerLeftProduct 0 27) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 28=f405desc10IntegerLeftProduct 0 28) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 29=f405desc10IntegerLeftProduct 0 29) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 30=f405desc10IntegerLeftProduct 0 30) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 31=f405desc10IntegerLeftProduct 0 31) := by
  decide +kernel

#print axioms f405desc10_left_row0_columns3

private theorem f405desc10_left_row0_columns4 :
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 32=f405desc10IntegerLeftProduct 0 32) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 33=f405desc10IntegerLeftProduct 0 33) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 34=f405desc10IntegerLeftProduct 0 34) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 35=f405desc10IntegerLeftProduct 0 35) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 36=f405desc10IntegerLeftProduct 0 36) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 37=f405desc10IntegerLeftProduct 0 37) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 38=f405desc10IntegerLeftProduct 0 38) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 39=f405desc10IntegerLeftProduct 0 39) := by
  decide +kernel

#print axioms f405desc10_left_row0_columns4

private theorem f405desc10_left_row0_columns5 :
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 40=f405desc10IntegerLeftProduct 0 40) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 41=f405desc10IntegerLeftProduct 0 41) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 42=f405desc10IntegerLeftProduct 0 42) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 43=f405desc10IntegerLeftProduct 0 43) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 44=f405desc10IntegerLeftProduct 0 44) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 45=f405desc10IntegerLeftProduct 0 45) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 46=f405desc10IntegerLeftProduct 0 46) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 47=f405desc10IntegerLeftProduct 0 47) := by
  decide +kernel

#print axioms f405desc10_left_row0_columns5

private theorem f405desc10_left_row0_columns6 :
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 48=f405desc10IntegerLeftProduct 0 48) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 49=f405desc10IntegerLeftProduct 0 49) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 50=f405desc10IntegerLeftProduct 0 50) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 51=f405desc10IntegerLeftProduct 0 51) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 52=f405desc10IntegerLeftProduct 0 52) ∧
    ((f405desc10IntegerCoordinatesᵀ*f415rawInteger) 0 53=f405desc10IntegerLeftProduct 0 53) := by
  decide +kernel

#print axioms f405desc10_left_row0_columns6

theorem f405desc10_compression_check :
    f405desc10ᵀ*f415rawM4Form*f405desc10=f405desc10Form := by
  have hD := f405desc10_coordinates_decode
  have hV : f405desc10IntegerCoordinatesᵀ*f415rawInteger=f405desc10IntegerLeftProduct := by
    ext a b
    fin_cases a
    · fin_cases b
      · exact f405desc10_left_row0_columns0.1
      · exact f405desc10_left_row0_columns0.2.1
      · exact f405desc10_left_row0_columns0.2.2.1
      · exact f405desc10_left_row0_columns0.2.2.2.1
      · exact f405desc10_left_row0_columns0.2.2.2.2.1
      · exact f405desc10_left_row0_columns0.2.2.2.2.2.1
      · exact f405desc10_left_row0_columns0.2.2.2.2.2.2.1
      · exact f405desc10_left_row0_columns0.2.2.2.2.2.2.2
      · exact f405desc10_left_row0_columns1.1
      · exact f405desc10_left_row0_columns1.2.1
      · exact f405desc10_left_row0_columns1.2.2.1
      · exact f405desc10_left_row0_columns1.2.2.2.1
      · exact f405desc10_left_row0_columns1.2.2.2.2.1
      · exact f405desc10_left_row0_columns1.2.2.2.2.2.1
      · exact f405desc10_left_row0_columns1.2.2.2.2.2.2.1
      · exact f405desc10_left_row0_columns1.2.2.2.2.2.2.2
      · exact f405desc10_left_row0_columns2.1
      · exact f405desc10_left_row0_columns2.2.1
      · exact f405desc10_left_row0_columns2.2.2.1
      · exact f405desc10_left_row0_columns2.2.2.2.1
      · exact f405desc10_left_row0_columns2.2.2.2.2.1
      · exact f405desc10_left_row0_columns2.2.2.2.2.2.1
      · exact f405desc10_left_row0_columns2.2.2.2.2.2.2.1
      · exact f405desc10_left_row0_columns2.2.2.2.2.2.2.2
      · exact f405desc10_left_row0_columns3.1
      · exact f405desc10_left_row0_columns3.2.1
      · exact f405desc10_left_row0_columns3.2.2.1
      · exact f405desc10_left_row0_columns3.2.2.2.1
      · exact f405desc10_left_row0_columns3.2.2.2.2.1
      · exact f405desc10_left_row0_columns3.2.2.2.2.2.1
      · exact f405desc10_left_row0_columns3.2.2.2.2.2.2.1
      · exact f405desc10_left_row0_columns3.2.2.2.2.2.2.2
      · exact f405desc10_left_row0_columns4.1
      · exact f405desc10_left_row0_columns4.2.1
      · exact f405desc10_left_row0_columns4.2.2.1
      · exact f405desc10_left_row0_columns4.2.2.2.1
      · exact f405desc10_left_row0_columns4.2.2.2.2.1
      · exact f405desc10_left_row0_columns4.2.2.2.2.2.1
      · exact f405desc10_left_row0_columns4.2.2.2.2.2.2.1
      · exact f405desc10_left_row0_columns4.2.2.2.2.2.2.2
      · exact f405desc10_left_row0_columns5.1
      · exact f405desc10_left_row0_columns5.2.1
      · exact f405desc10_left_row0_columns5.2.2.1
      · exact f405desc10_left_row0_columns5.2.2.2.1
      · exact f405desc10_left_row0_columns5.2.2.2.2.1
      · exact f405desc10_left_row0_columns5.2.2.2.2.2.1
      · exact f405desc10_left_row0_columns5.2.2.2.2.2.2.1
      · exact f405desc10_left_row0_columns5.2.2.2.2.2.2.2
      · exact f405desc10_left_row0_columns6.1
      · exact f405desc10_left_row0_columns6.2.1
      · exact f405desc10_left_row0_columns6.2.2.1
      · exact f405desc10_left_row0_columns6.2.2.2.1
      · exact f405desc10_left_row0_columns6.2.2.2.2.1
      · exact f405desc10_left_row0_columns6.2.2.2.2.2
  have hY : f405desc10IntegerLeftProduct*f405desc10IntegerCoordinates=f405desc10IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f405desc10IntegerLeftProduct*f405desc10IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f405desc10IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (6*1000000000000000000000000*6) f405desc10IntegerForm=f405desc10Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (6*1000000000000000000000000*6) f405desc10IntegerForm) (f405desc10Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 6
    f415rawInteger f405desc10IntegerCoordinates f405desc10IntegerLeftProduct f405desc10IntegerForm
    f415rawM4Form f405desc10 f405desc10Form f415_raw_integer_check hD hV hY hF

theorem f405desc10_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[10] (natFourWordBlock f405basis (complexify b405relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[10]
          (natFourWordBlock f405basis (complexify b405relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f405desc10Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 10
    f405basis b405relative
    f415basis f405desc10 f415rawM4Form f405desc10Form
    f405desc10_actual f415_actual_raw_M4_matrix f405desc10_compression_check x y


#print axioms f405desc10_compression_check
#print axioms f405desc10_source_form
end TorusLean.BosonFiniteCertificate
