import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates405
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger414
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

def f405desc9Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(69713680175000070830492242779/78125000000000000000)]

private def f405desc9IntegerCoordinates : Matrix (Fin 47) (Fin 1) ℤ :=
  !![(-1);
    (-22);
    (-65);
    (-92);
    (-43);
    54;
    111;
    60;
    (-134);
    (-600);
    (-472);
    268;
    684;
    432;
    (-354);
    776;
    2466;
    1872;
    420;
    2004;
    5136;
    3024;
    2394;
    1764;
    (-216);
    (-972);
    (-104);
    486;
    (-1296);
    (-1428);
    (-156);
    4104;
    (-432);
    (-13104);
    2592;
    (-7728);
    (-9072);
    (-8316);
    1026;
    3888;
    (-5796);
    (-6804);
    2352;
    (-3024);
    1890;
    6048;
    16380]

private def f405desc9IntegerLeftProduct : Matrix (Fin 1) (Fin 47) ℤ :=
  !![0, 0, 0, 0, 0, 0, 10316849181819122554489886515200, 136061657968031943953257583308800, 0, 0, 0, 0, 394688854728757770587036467200, 15047872150348467164862254822400, 0, 0, (-345975324103375647879673036800), 819911456430468098848997529600, 3957676079428120344141011097600, (-17154334004372052251065344000), 16246853583744517309716940800, (-2930076281863560535941358540800), 2943894733546295236044533990400, 0, 0, 0, 0, (-50934172025903928866205696000), (-19048156935238183776970060800), 613033148573495580488217292800, 0, 27563812995956443763610009600, 282238697227077177861665664000, (-2744212730232375744565752806400), (-1253010977706441773810529100800), 203930243520794142190500787200, 0, 0, (-222759192081186779235181977600), (-148059520697402830632612787200), 2062115260579291315392503424000, 0, (-863712781077394569837135513600), 0, 0, 0, 0]

private def f405desc9IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![32124063824640032638690825472563200]

private theorem f405desc9_coordinates_decode : natFourIntegerMatrix 6 f405desc9IntegerCoordinates=f405desc9 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 6 f405desc9IntegerCoordinates) (f405desc9) (by decide +kernel) a b

#print axioms f405desc9_coordinates_decode

private theorem f405desc9_left_row0_columns0 :
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 0=f405desc9IntegerLeftProduct 0 0) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 1=f405desc9IntegerLeftProduct 0 1) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 2=f405desc9IntegerLeftProduct 0 2) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 3=f405desc9IntegerLeftProduct 0 3) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 4=f405desc9IntegerLeftProduct 0 4) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 5=f405desc9IntegerLeftProduct 0 5) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 6=f405desc9IntegerLeftProduct 0 6) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 7=f405desc9IntegerLeftProduct 0 7) := by
  decide +kernel

#print axioms f405desc9_left_row0_columns0

private theorem f405desc9_left_row0_columns1 :
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 8=f405desc9IntegerLeftProduct 0 8) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 9=f405desc9IntegerLeftProduct 0 9) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 10=f405desc9IntegerLeftProduct 0 10) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 11=f405desc9IntegerLeftProduct 0 11) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 12=f405desc9IntegerLeftProduct 0 12) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 13=f405desc9IntegerLeftProduct 0 13) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 14=f405desc9IntegerLeftProduct 0 14) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 15=f405desc9IntegerLeftProduct 0 15) := by
  decide +kernel

#print axioms f405desc9_left_row0_columns1

private theorem f405desc9_left_row0_columns2 :
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 16=f405desc9IntegerLeftProduct 0 16) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 17=f405desc9IntegerLeftProduct 0 17) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 18=f405desc9IntegerLeftProduct 0 18) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 19=f405desc9IntegerLeftProduct 0 19) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 20=f405desc9IntegerLeftProduct 0 20) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 21=f405desc9IntegerLeftProduct 0 21) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 22=f405desc9IntegerLeftProduct 0 22) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 23=f405desc9IntegerLeftProduct 0 23) := by
  decide +kernel

#print axioms f405desc9_left_row0_columns2

private theorem f405desc9_left_row0_columns3 :
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 24=f405desc9IntegerLeftProduct 0 24) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 25=f405desc9IntegerLeftProduct 0 25) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 26=f405desc9IntegerLeftProduct 0 26) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 27=f405desc9IntegerLeftProduct 0 27) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 28=f405desc9IntegerLeftProduct 0 28) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 29=f405desc9IntegerLeftProduct 0 29) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 30=f405desc9IntegerLeftProduct 0 30) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 31=f405desc9IntegerLeftProduct 0 31) := by
  decide +kernel

#print axioms f405desc9_left_row0_columns3

private theorem f405desc9_left_row0_columns4 :
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 32=f405desc9IntegerLeftProduct 0 32) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 33=f405desc9IntegerLeftProduct 0 33) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 34=f405desc9IntegerLeftProduct 0 34) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 35=f405desc9IntegerLeftProduct 0 35) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 36=f405desc9IntegerLeftProduct 0 36) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 37=f405desc9IntegerLeftProduct 0 37) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 38=f405desc9IntegerLeftProduct 0 38) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 39=f405desc9IntegerLeftProduct 0 39) := by
  decide +kernel

#print axioms f405desc9_left_row0_columns4

private theorem f405desc9_left_row0_columns5 :
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 40=f405desc9IntegerLeftProduct 0 40) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 41=f405desc9IntegerLeftProduct 0 41) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 42=f405desc9IntegerLeftProduct 0 42) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 43=f405desc9IntegerLeftProduct 0 43) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 44=f405desc9IntegerLeftProduct 0 44) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 45=f405desc9IntegerLeftProduct 0 45) ∧
    ((f405desc9IntegerCoordinatesᵀ*f414rawInteger) 0 46=f405desc9IntegerLeftProduct 0 46) := by
  decide +kernel

#print axioms f405desc9_left_row0_columns5

theorem f405desc9_compression_check :
    f405desc9ᵀ*f414rawM4Form*f405desc9=f405desc9Form := by
  have hD := f405desc9_coordinates_decode
  have hV : f405desc9IntegerCoordinatesᵀ*f414rawInteger=f405desc9IntegerLeftProduct := by
    ext a b
    fin_cases a
    · fin_cases b
      · exact f405desc9_left_row0_columns0.1
      · exact f405desc9_left_row0_columns0.2.1
      · exact f405desc9_left_row0_columns0.2.2.1
      · exact f405desc9_left_row0_columns0.2.2.2.1
      · exact f405desc9_left_row0_columns0.2.2.2.2.1
      · exact f405desc9_left_row0_columns0.2.2.2.2.2.1
      · exact f405desc9_left_row0_columns0.2.2.2.2.2.2.1
      · exact f405desc9_left_row0_columns0.2.2.2.2.2.2.2
      · exact f405desc9_left_row0_columns1.1
      · exact f405desc9_left_row0_columns1.2.1
      · exact f405desc9_left_row0_columns1.2.2.1
      · exact f405desc9_left_row0_columns1.2.2.2.1
      · exact f405desc9_left_row0_columns1.2.2.2.2.1
      · exact f405desc9_left_row0_columns1.2.2.2.2.2.1
      · exact f405desc9_left_row0_columns1.2.2.2.2.2.2.1
      · exact f405desc9_left_row0_columns1.2.2.2.2.2.2.2
      · exact f405desc9_left_row0_columns2.1
      · exact f405desc9_left_row0_columns2.2.1
      · exact f405desc9_left_row0_columns2.2.2.1
      · exact f405desc9_left_row0_columns2.2.2.2.1
      · exact f405desc9_left_row0_columns2.2.2.2.2.1
      · exact f405desc9_left_row0_columns2.2.2.2.2.2.1
      · exact f405desc9_left_row0_columns2.2.2.2.2.2.2.1
      · exact f405desc9_left_row0_columns2.2.2.2.2.2.2.2
      · exact f405desc9_left_row0_columns3.1
      · exact f405desc9_left_row0_columns3.2.1
      · exact f405desc9_left_row0_columns3.2.2.1
      · exact f405desc9_left_row0_columns3.2.2.2.1
      · exact f405desc9_left_row0_columns3.2.2.2.2.1
      · exact f405desc9_left_row0_columns3.2.2.2.2.2.1
      · exact f405desc9_left_row0_columns3.2.2.2.2.2.2.1
      · exact f405desc9_left_row0_columns3.2.2.2.2.2.2.2
      · exact f405desc9_left_row0_columns4.1
      · exact f405desc9_left_row0_columns4.2.1
      · exact f405desc9_left_row0_columns4.2.2.1
      · exact f405desc9_left_row0_columns4.2.2.2.1
      · exact f405desc9_left_row0_columns4.2.2.2.2.1
      · exact f405desc9_left_row0_columns4.2.2.2.2.2.1
      · exact f405desc9_left_row0_columns4.2.2.2.2.2.2.1
      · exact f405desc9_left_row0_columns4.2.2.2.2.2.2.2
      · exact f405desc9_left_row0_columns5.1
      · exact f405desc9_left_row0_columns5.2.1
      · exact f405desc9_left_row0_columns5.2.2.1
      · exact f405desc9_left_row0_columns5.2.2.2.1
      · exact f405desc9_left_row0_columns5.2.2.2.2.1
      · exact f405desc9_left_row0_columns5.2.2.2.2.2.1
      · exact f405desc9_left_row0_columns5.2.2.2.2.2.2
  have hY : f405desc9IntegerLeftProduct*f405desc9IntegerCoordinates=f405desc9IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f405desc9IntegerLeftProduct*f405desc9IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f405desc9IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (6*1000000000000000000000000*6) f405desc9IntegerForm=f405desc9Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (6*1000000000000000000000000*6) f405desc9IntegerForm) (f405desc9Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 6
    f414rawInteger f405desc9IntegerCoordinates f405desc9IntegerLeftProduct f405desc9IntegerForm
    f414rawM4Form f405desc9 f405desc9Form f414_raw_integer_check hD hV hY hF

theorem f405desc9_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[9] (natFourWordBlock f405basis (complexify b405relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[9]
          (natFourWordBlock f405basis (complexify b405relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f405desc9Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 9
    f405basis b405relative
    f414basis f405desc9 f414rawM4Form f405desc9Form
    f405desc9_actual f414_actual_raw_M4_matrix f405desc9_compression_check x y


#print axioms f405desc9_compression_check
#print axioms f405desc9_source_form
end TorusLean.BosonFiniteCertificate
