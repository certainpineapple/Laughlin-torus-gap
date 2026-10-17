import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates403
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger414
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

def f403desc11Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(77253019763226293936394985623831/15625000000000000000)]

private def f403desc11IntegerCoordinates : Matrix (Fin 47) (Fin 1) ℤ :=
  !![1;
    30;
    129;
    300;
    363;
    66;
    (-495);
    (-396);
    270;
    2040;
    3960;
    3300;
    (-1980);
    (-7920);
    3234;
    9240;
    990;
    (-17424);
    (-13860);
    1980;
    (-23760);
    (-55440);
    (-34650);
    (-47124);
    728;
    7260;
    11880;
    6930;
    (-7920);
    (-8316);
    20460;
    51480;
    7920;
    (-55440);
    15840;
    (-55440);
    (-55440);
    (-69300);
    16830;
    55440;
    13860;
    (-8316);
    55440;
    55440;
    11550;
    36960;
    69300]

private def f403desc11IntegerLeftProduct : Matrix (Fin 1) (Fin 47) ℤ :=
  !![0, 0, 0, 0, 0, 0, (-1668499957803892437600091864473600), (-2411633058970505430428542482739200), 0, 0, 0, 0, (-3417793768522139495849050521600), (-788576732981623794142859765068800), 0, 0, 2995960518641412047418668236800, (-35534767993177650615899037849600), (-301118399276275335897311051520000), 148547254083285738995216179200, (-7863098114839261882755528345600), (-57601453314124744328992601548800), 48899003786018003560547539123200, 0, 0, 0, 0, 441062515065402996809999155200, (-20322244302603411193274235571200), (-349666242506968899811903302758400), 0, (-238687861535685089302660300800), (-10888098448836748419484577049600), (-45391747969412101708740989568000), 17630953695777318112747610956800, 5098905564274200483934061644800, 0, 0, 1928975026421353133008132300800, (-606570328794407846606240025600), 41582532524333625061481799244800, 0, (-14427271042122820635383290214400), 0, 0, 0, 0]

private def f403desc11IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![19776773059385931247717116319700736000]

private theorem f403desc11_coordinates_decode : natFourIntegerMatrix 2 f403desc11IntegerCoordinates=f403desc11 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 2 f403desc11IntegerCoordinates) (f403desc11) (by decide +kernel) a b

#print axioms f403desc11_coordinates_decode

private theorem f403desc11_left_row0_columns0 :
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 0=f403desc11IntegerLeftProduct 0 0) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 1=f403desc11IntegerLeftProduct 0 1) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 2=f403desc11IntegerLeftProduct 0 2) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 3=f403desc11IntegerLeftProduct 0 3) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 4=f403desc11IntegerLeftProduct 0 4) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 5=f403desc11IntegerLeftProduct 0 5) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 6=f403desc11IntegerLeftProduct 0 6) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 7=f403desc11IntegerLeftProduct 0 7) := by
  decide +kernel

#print axioms f403desc11_left_row0_columns0

private theorem f403desc11_left_row0_columns1 :
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 8=f403desc11IntegerLeftProduct 0 8) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 9=f403desc11IntegerLeftProduct 0 9) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 10=f403desc11IntegerLeftProduct 0 10) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 11=f403desc11IntegerLeftProduct 0 11) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 12=f403desc11IntegerLeftProduct 0 12) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 13=f403desc11IntegerLeftProduct 0 13) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 14=f403desc11IntegerLeftProduct 0 14) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 15=f403desc11IntegerLeftProduct 0 15) := by
  decide +kernel

#print axioms f403desc11_left_row0_columns1

private theorem f403desc11_left_row0_columns2 :
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 16=f403desc11IntegerLeftProduct 0 16) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 17=f403desc11IntegerLeftProduct 0 17) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 18=f403desc11IntegerLeftProduct 0 18) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 19=f403desc11IntegerLeftProduct 0 19) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 20=f403desc11IntegerLeftProduct 0 20) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 21=f403desc11IntegerLeftProduct 0 21) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 22=f403desc11IntegerLeftProduct 0 22) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 23=f403desc11IntegerLeftProduct 0 23) := by
  decide +kernel

#print axioms f403desc11_left_row0_columns2

private theorem f403desc11_left_row0_columns3 :
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 24=f403desc11IntegerLeftProduct 0 24) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 25=f403desc11IntegerLeftProduct 0 25) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 26=f403desc11IntegerLeftProduct 0 26) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 27=f403desc11IntegerLeftProduct 0 27) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 28=f403desc11IntegerLeftProduct 0 28) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 29=f403desc11IntegerLeftProduct 0 29) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 30=f403desc11IntegerLeftProduct 0 30) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 31=f403desc11IntegerLeftProduct 0 31) := by
  decide +kernel

#print axioms f403desc11_left_row0_columns3

private theorem f403desc11_left_row0_columns4 :
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 32=f403desc11IntegerLeftProduct 0 32) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 33=f403desc11IntegerLeftProduct 0 33) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 34=f403desc11IntegerLeftProduct 0 34) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 35=f403desc11IntegerLeftProduct 0 35) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 36=f403desc11IntegerLeftProduct 0 36) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 37=f403desc11IntegerLeftProduct 0 37) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 38=f403desc11IntegerLeftProduct 0 38) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 39=f403desc11IntegerLeftProduct 0 39) := by
  decide +kernel

#print axioms f403desc11_left_row0_columns4

private theorem f403desc11_left_row0_columns5 :
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 40=f403desc11IntegerLeftProduct 0 40) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 41=f403desc11IntegerLeftProduct 0 41) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 42=f403desc11IntegerLeftProduct 0 42) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 43=f403desc11IntegerLeftProduct 0 43) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 44=f403desc11IntegerLeftProduct 0 44) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 45=f403desc11IntegerLeftProduct 0 45) ∧
    ((f403desc11IntegerCoordinatesᵀ*f414rawInteger) 0 46=f403desc11IntegerLeftProduct 0 46) := by
  decide +kernel

#print axioms f403desc11_left_row0_columns5

theorem f403desc11_compression_check :
    f403desc11ᵀ*f414rawM4Form*f403desc11=f403desc11Form := by
  have hD := f403desc11_coordinates_decode
  have hV : f403desc11IntegerCoordinatesᵀ*f414rawInteger=f403desc11IntegerLeftProduct := by
    ext a b
    fin_cases a
    · fin_cases b
      · exact f403desc11_left_row0_columns0.1
      · exact f403desc11_left_row0_columns0.2.1
      · exact f403desc11_left_row0_columns0.2.2.1
      · exact f403desc11_left_row0_columns0.2.2.2.1
      · exact f403desc11_left_row0_columns0.2.2.2.2.1
      · exact f403desc11_left_row0_columns0.2.2.2.2.2.1
      · exact f403desc11_left_row0_columns0.2.2.2.2.2.2.1
      · exact f403desc11_left_row0_columns0.2.2.2.2.2.2.2
      · exact f403desc11_left_row0_columns1.1
      · exact f403desc11_left_row0_columns1.2.1
      · exact f403desc11_left_row0_columns1.2.2.1
      · exact f403desc11_left_row0_columns1.2.2.2.1
      · exact f403desc11_left_row0_columns1.2.2.2.2.1
      · exact f403desc11_left_row0_columns1.2.2.2.2.2.1
      · exact f403desc11_left_row0_columns1.2.2.2.2.2.2.1
      · exact f403desc11_left_row0_columns1.2.2.2.2.2.2.2
      · exact f403desc11_left_row0_columns2.1
      · exact f403desc11_left_row0_columns2.2.1
      · exact f403desc11_left_row0_columns2.2.2.1
      · exact f403desc11_left_row0_columns2.2.2.2.1
      · exact f403desc11_left_row0_columns2.2.2.2.2.1
      · exact f403desc11_left_row0_columns2.2.2.2.2.2.1
      · exact f403desc11_left_row0_columns2.2.2.2.2.2.2.1
      · exact f403desc11_left_row0_columns2.2.2.2.2.2.2.2
      · exact f403desc11_left_row0_columns3.1
      · exact f403desc11_left_row0_columns3.2.1
      · exact f403desc11_left_row0_columns3.2.2.1
      · exact f403desc11_left_row0_columns3.2.2.2.1
      · exact f403desc11_left_row0_columns3.2.2.2.2.1
      · exact f403desc11_left_row0_columns3.2.2.2.2.2.1
      · exact f403desc11_left_row0_columns3.2.2.2.2.2.2.1
      · exact f403desc11_left_row0_columns3.2.2.2.2.2.2.2
      · exact f403desc11_left_row0_columns4.1
      · exact f403desc11_left_row0_columns4.2.1
      · exact f403desc11_left_row0_columns4.2.2.1
      · exact f403desc11_left_row0_columns4.2.2.2.1
      · exact f403desc11_left_row0_columns4.2.2.2.2.1
      · exact f403desc11_left_row0_columns4.2.2.2.2.2.1
      · exact f403desc11_left_row0_columns4.2.2.2.2.2.2.1
      · exact f403desc11_left_row0_columns4.2.2.2.2.2.2.2
      · exact f403desc11_left_row0_columns5.1
      · exact f403desc11_left_row0_columns5.2.1
      · exact f403desc11_left_row0_columns5.2.2.1
      · exact f403desc11_left_row0_columns5.2.2.2.1
      · exact f403desc11_left_row0_columns5.2.2.2.2.1
      · exact f403desc11_left_row0_columns5.2.2.2.2.2.1
      · exact f403desc11_left_row0_columns5.2.2.2.2.2.2
  have hY : f403desc11IntegerLeftProduct*f403desc11IntegerCoordinates=f403desc11IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc11IntegerLeftProduct*f403desc11IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc11IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc11IntegerForm=f403desc11Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc11IntegerForm) (f403desc11Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 2
    f414rawInteger f403desc11IntegerCoordinates f403desc11IntegerLeftProduct f403desc11IntegerForm
    f414rawM4Form f403desc11 f403desc11Form f414_raw_integer_check hD hV hY hF

theorem f403desc11_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[11] (natFourWordBlock f403basis (complexify b403relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[11]
          (natFourWordBlock f403basis (complexify b403relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f403desc11Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 11
    f403basis b403relative
    f414basis f403desc11 f414rawM4Form f403desc11Form
    f403desc11_actual f414_actual_raw_M4_matrix f403desc11_compression_check x y


#print axioms f403desc11_compression_check
#print axioms f403desc11_source_form
end TorusLean.BosonFiniteCertificate
