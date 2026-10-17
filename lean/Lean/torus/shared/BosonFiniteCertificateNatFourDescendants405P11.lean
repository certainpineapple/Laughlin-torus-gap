import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates405
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger416
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

def f405desc11Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(768079850422658023461063699/305175781250000000)]

private def f405desc11IntegerCoordinates : Matrix (Fin 64) (Fin 1) ℤ :=
  !![(-1);
    (-28);
    (-112);
    (-244);
    (-292);
    (-124);
    176;
    396;
    231;
    (-228);
    (-1528);
    (-2568);
    (-1816);
    792;
    2728;
    2904;
    (-1952);
    (-3568);
    2816;
    9592;
    9504;
    3696;
    2376;
    20680;
    26664;
    20064;
    19140;
    36432;
    14784;
    16632;
    (-528);
    (-4268);
    (-5024);
    (-1188);
    1584;
    (-2508);
    (-3168);
    (-7848);
    (-4048);
    16280;
    (-2376);
    (-49632);
    15840;
    38280;
    (-38016);
    (-48048);
    (-3960);
    (-99792);
    (-22176);
    (-1584);
    18040;
    15840;
    (-49104);
    (-48048);
    43560;
    5280;
    (-170016);
    (-36960);
    (-60984);
    21120;
    55440;
    22176;
    194040;
    34650]

private def f405desc11IntegerLeftProduct : Matrix (Fin 1) (Fin 64) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, (-394125640758415519563526963200), 0, 0, 0, 0, 0, 0, 42269973572089922648748569395200, 0, 0, 0, 0, (-6263782294487563785276584755200), 0, 0, 0, 1506122921434245013651459276800, 0, (-1027541812777805567283432652800), 0, 0, 0, 0, 0, 0, 0, 0, (-5841504848229810505813160755200), 0, 0, 0, 0, 1365363775655265903620073062400, 0, 0, (-154835065569923293835427840000), 0, 0, 0, 0, 0, 0, 0, (-717871657606655683330238054400), 0, 0, 295594235380205700149152972800, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def f405desc11IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![90606385939138769205979687039795200]

private theorem f405desc11_coordinates_decode : natFourIntegerMatrix 6 f405desc11IntegerCoordinates=f405desc11 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 6 f405desc11IntegerCoordinates) (f405desc11) (by decide +kernel) a b

#print axioms f405desc11_coordinates_decode

private theorem f405desc11_left_row0_columns0 :
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 0=f405desc11IntegerLeftProduct 0 0) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 1=f405desc11IntegerLeftProduct 0 1) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 2=f405desc11IntegerLeftProduct 0 2) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 3=f405desc11IntegerLeftProduct 0 3) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 4=f405desc11IntegerLeftProduct 0 4) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 5=f405desc11IntegerLeftProduct 0 5) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 6=f405desc11IntegerLeftProduct 0 6) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 7=f405desc11IntegerLeftProduct 0 7) := by
  decide +kernel

#print axioms f405desc11_left_row0_columns0

private theorem f405desc11_left_row0_columns1 :
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 8=f405desc11IntegerLeftProduct 0 8) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 9=f405desc11IntegerLeftProduct 0 9) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 10=f405desc11IntegerLeftProduct 0 10) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 11=f405desc11IntegerLeftProduct 0 11) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 12=f405desc11IntegerLeftProduct 0 12) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 13=f405desc11IntegerLeftProduct 0 13) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 14=f405desc11IntegerLeftProduct 0 14) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 15=f405desc11IntegerLeftProduct 0 15) := by
  decide +kernel

#print axioms f405desc11_left_row0_columns1

private theorem f405desc11_left_row0_columns2 :
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 16=f405desc11IntegerLeftProduct 0 16) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 17=f405desc11IntegerLeftProduct 0 17) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 18=f405desc11IntegerLeftProduct 0 18) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 19=f405desc11IntegerLeftProduct 0 19) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 20=f405desc11IntegerLeftProduct 0 20) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 21=f405desc11IntegerLeftProduct 0 21) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 22=f405desc11IntegerLeftProduct 0 22) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 23=f405desc11IntegerLeftProduct 0 23) := by
  decide +kernel

#print axioms f405desc11_left_row0_columns2

private theorem f405desc11_left_row0_columns3 :
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 24=f405desc11IntegerLeftProduct 0 24) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 25=f405desc11IntegerLeftProduct 0 25) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 26=f405desc11IntegerLeftProduct 0 26) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 27=f405desc11IntegerLeftProduct 0 27) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 28=f405desc11IntegerLeftProduct 0 28) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 29=f405desc11IntegerLeftProduct 0 29) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 30=f405desc11IntegerLeftProduct 0 30) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 31=f405desc11IntegerLeftProduct 0 31) := by
  decide +kernel

#print axioms f405desc11_left_row0_columns3

private theorem f405desc11_left_row0_columns4 :
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 32=f405desc11IntegerLeftProduct 0 32) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 33=f405desc11IntegerLeftProduct 0 33) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 34=f405desc11IntegerLeftProduct 0 34) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 35=f405desc11IntegerLeftProduct 0 35) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 36=f405desc11IntegerLeftProduct 0 36) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 37=f405desc11IntegerLeftProduct 0 37) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 38=f405desc11IntegerLeftProduct 0 38) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 39=f405desc11IntegerLeftProduct 0 39) := by
  decide +kernel

#print axioms f405desc11_left_row0_columns4

private theorem f405desc11_left_row0_columns5 :
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 40=f405desc11IntegerLeftProduct 0 40) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 41=f405desc11IntegerLeftProduct 0 41) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 42=f405desc11IntegerLeftProduct 0 42) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 43=f405desc11IntegerLeftProduct 0 43) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 44=f405desc11IntegerLeftProduct 0 44) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 45=f405desc11IntegerLeftProduct 0 45) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 46=f405desc11IntegerLeftProduct 0 46) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 47=f405desc11IntegerLeftProduct 0 47) := by
  decide +kernel

#print axioms f405desc11_left_row0_columns5

private theorem f405desc11_left_row0_columns6 :
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 48=f405desc11IntegerLeftProduct 0 48) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 49=f405desc11IntegerLeftProduct 0 49) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 50=f405desc11IntegerLeftProduct 0 50) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 51=f405desc11IntegerLeftProduct 0 51) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 52=f405desc11IntegerLeftProduct 0 52) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 53=f405desc11IntegerLeftProduct 0 53) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 54=f405desc11IntegerLeftProduct 0 54) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 55=f405desc11IntegerLeftProduct 0 55) := by
  decide +kernel

#print axioms f405desc11_left_row0_columns6

private theorem f405desc11_left_row0_columns7 :
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 56=f405desc11IntegerLeftProduct 0 56) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 57=f405desc11IntegerLeftProduct 0 57) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 58=f405desc11IntegerLeftProduct 0 58) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 59=f405desc11IntegerLeftProduct 0 59) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 60=f405desc11IntegerLeftProduct 0 60) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 61=f405desc11IntegerLeftProduct 0 61) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 62=f405desc11IntegerLeftProduct 0 62) ∧
    ((f405desc11IntegerCoordinatesᵀ*f416rawInteger) 0 63=f405desc11IntegerLeftProduct 0 63) := by
  decide +kernel

#print axioms f405desc11_left_row0_columns7

theorem f405desc11_compression_check :
    f405desc11ᵀ*f416rawM4Form*f405desc11=f405desc11Form := by
  have hD := f405desc11_coordinates_decode
  have hV : f405desc11IntegerCoordinatesᵀ*f416rawInteger=f405desc11IntegerLeftProduct := by
    ext a b
    fin_cases a
    · fin_cases b
      · exact f405desc11_left_row0_columns0.1
      · exact f405desc11_left_row0_columns0.2.1
      · exact f405desc11_left_row0_columns0.2.2.1
      · exact f405desc11_left_row0_columns0.2.2.2.1
      · exact f405desc11_left_row0_columns0.2.2.2.2.1
      · exact f405desc11_left_row0_columns0.2.2.2.2.2.1
      · exact f405desc11_left_row0_columns0.2.2.2.2.2.2.1
      · exact f405desc11_left_row0_columns0.2.2.2.2.2.2.2
      · exact f405desc11_left_row0_columns1.1
      · exact f405desc11_left_row0_columns1.2.1
      · exact f405desc11_left_row0_columns1.2.2.1
      · exact f405desc11_left_row0_columns1.2.2.2.1
      · exact f405desc11_left_row0_columns1.2.2.2.2.1
      · exact f405desc11_left_row0_columns1.2.2.2.2.2.1
      · exact f405desc11_left_row0_columns1.2.2.2.2.2.2.1
      · exact f405desc11_left_row0_columns1.2.2.2.2.2.2.2
      · exact f405desc11_left_row0_columns2.1
      · exact f405desc11_left_row0_columns2.2.1
      · exact f405desc11_left_row0_columns2.2.2.1
      · exact f405desc11_left_row0_columns2.2.2.2.1
      · exact f405desc11_left_row0_columns2.2.2.2.2.1
      · exact f405desc11_left_row0_columns2.2.2.2.2.2.1
      · exact f405desc11_left_row0_columns2.2.2.2.2.2.2.1
      · exact f405desc11_left_row0_columns2.2.2.2.2.2.2.2
      · exact f405desc11_left_row0_columns3.1
      · exact f405desc11_left_row0_columns3.2.1
      · exact f405desc11_left_row0_columns3.2.2.1
      · exact f405desc11_left_row0_columns3.2.2.2.1
      · exact f405desc11_left_row0_columns3.2.2.2.2.1
      · exact f405desc11_left_row0_columns3.2.2.2.2.2.1
      · exact f405desc11_left_row0_columns3.2.2.2.2.2.2.1
      · exact f405desc11_left_row0_columns3.2.2.2.2.2.2.2
      · exact f405desc11_left_row0_columns4.1
      · exact f405desc11_left_row0_columns4.2.1
      · exact f405desc11_left_row0_columns4.2.2.1
      · exact f405desc11_left_row0_columns4.2.2.2.1
      · exact f405desc11_left_row0_columns4.2.2.2.2.1
      · exact f405desc11_left_row0_columns4.2.2.2.2.2.1
      · exact f405desc11_left_row0_columns4.2.2.2.2.2.2.1
      · exact f405desc11_left_row0_columns4.2.2.2.2.2.2.2
      · exact f405desc11_left_row0_columns5.1
      · exact f405desc11_left_row0_columns5.2.1
      · exact f405desc11_left_row0_columns5.2.2.1
      · exact f405desc11_left_row0_columns5.2.2.2.1
      · exact f405desc11_left_row0_columns5.2.2.2.2.1
      · exact f405desc11_left_row0_columns5.2.2.2.2.2.1
      · exact f405desc11_left_row0_columns5.2.2.2.2.2.2.1
      · exact f405desc11_left_row0_columns5.2.2.2.2.2.2.2
      · exact f405desc11_left_row0_columns6.1
      · exact f405desc11_left_row0_columns6.2.1
      · exact f405desc11_left_row0_columns6.2.2.1
      · exact f405desc11_left_row0_columns6.2.2.2.1
      · exact f405desc11_left_row0_columns6.2.2.2.2.1
      · exact f405desc11_left_row0_columns6.2.2.2.2.2.1
      · exact f405desc11_left_row0_columns6.2.2.2.2.2.2.1
      · exact f405desc11_left_row0_columns6.2.2.2.2.2.2.2
      · exact f405desc11_left_row0_columns7.1
      · exact f405desc11_left_row0_columns7.2.1
      · exact f405desc11_left_row0_columns7.2.2.1
      · exact f405desc11_left_row0_columns7.2.2.2.1
      · exact f405desc11_left_row0_columns7.2.2.2.2.1
      · exact f405desc11_left_row0_columns7.2.2.2.2.2.1
      · exact f405desc11_left_row0_columns7.2.2.2.2.2.2.1
      · exact f405desc11_left_row0_columns7.2.2.2.2.2.2.2
  have hY : f405desc11IntegerLeftProduct*f405desc11IntegerCoordinates=f405desc11IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f405desc11IntegerLeftProduct*f405desc11IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f405desc11IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (6*1000000000000000000000000*6) f405desc11IntegerForm=f405desc11Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (6*1000000000000000000000000*6) f405desc11IntegerForm) (f405desc11Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 6
    f416rawInteger f405desc11IntegerCoordinates f405desc11IntegerLeftProduct f405desc11IntegerForm
    f416rawM4Form f405desc11 f405desc11Form f416_raw_integer_check hD hV hY hF

theorem f405desc11_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[11] (natFourWordBlock f405basis (complexify b405relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[11]
          (natFourWordBlock f405basis (complexify b405relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f405desc11Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 11
    f405basis b405relative
    f416basis f405desc11 f416rawM4Form f405desc11Form
    f405desc11_actual f416_actual_raw_M4_matrix f405desc11_compression_check x y


#print axioms f405desc11_compression_check
#print axioms f405desc11_source_form
end TorusLean.BosonFiniteCertificate
