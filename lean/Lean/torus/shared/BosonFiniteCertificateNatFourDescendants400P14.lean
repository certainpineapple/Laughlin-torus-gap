import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates400
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger414
import torus.shared.BosonFiniteCertificateNatFourRaise400
import torus.shared.BosonFiniteCertificateNatFourRaise401
import torus.shared.BosonFiniteCertificateNatFourRaise402
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
import torus.shared.BosonFiniteCertificate400

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

def f400desc14Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(278533547886586856393821231341772371/1220703125000000000)]

private def f400desc14IntegerCoordinates : Matrix (Fin 47) (Fin 1) ℤ :=
  !![4;
    168;
    1092;
    4368;
    12012;
    24024;
    36036;
    20592;
    2184;
    26208;
    96096;
    240240;
    432432;
    576576;
    72072;
    480480;
    1081080;
    1729728;
    1009008;
    720720;
    2882880;
    4036032;
    2522520;
    3027024;
    8736;
    144144;
    480480;
    1081080;
    1729728;
    1009008;
    720720;
    4324320;
    8648640;
    12108096;
    5765760;
    20180160;
    12108096;
    15135120;
    1081080;
    8648640;
    15135120;
    9081072;
    20180160;
    60540480;
    12612600;
    13453440;
    25225200]

private def f400desc14IntegerLeftProduct : Matrix (Fin 1) (Fin 47) ℤ :=
  !![0, 0, 0, 0, 0, 0, 114780262745280867605051767300915200, 162292789681827957339628747725619200, 0, 0, 0, 0, 236430939218062668700071164313600, 54279958183304433392253537595699200, 0, 0, (-207249983851090160776973790412800), 3497792018257153802081357875814400, 24020658869099460696350657558323200, (-10275969294053877805598733926400), 1597473508172623745539691444428800, 5498158539838891966017103744819200, (-3123458897044195784944644622848000), 0, 0, 0, 0, (-30511115258491946562582351052800), 2414451295290463151712535119974400, 28164017782867491297026330594918400, 0, 16511606456659458641743454208000, 1886258665258757222263741886976000, 4724322147970654666937030692761600, (-101219736687730066384402436812800), 604616099979271046124825445478400, 0, 0, (-133439686385225419125305797017600), 1270906143365094060708470761574400, (-2240899748772981553293084124876800), 0, 2261011640118722576856458995507200, 0, 0, 0, 0]

private def f400desc14IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![228174682428691952757818352715179926323200]

private theorem f400desc14_coordinates_decode : natFourIntegerMatrix 1 f400desc14IntegerCoordinates=f400desc14 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f400desc14IntegerCoordinates) (f400desc14) (by decide +kernel) a b

#print axioms f400desc14_coordinates_decode

private theorem f400desc14_left_columns0 :
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 0=f400desc14IntegerLeftProduct 0 0) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 1=f400desc14IntegerLeftProduct 0 1) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 2=f400desc14IntegerLeftProduct 0 2) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 3=f400desc14IntegerLeftProduct 0 3) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 4=f400desc14IntegerLeftProduct 0 4) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 5=f400desc14IntegerLeftProduct 0 5) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 6=f400desc14IntegerLeftProduct 0 6) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 7=f400desc14IntegerLeftProduct 0 7) := by
  decide +kernel

#print axioms f400desc14_left_columns0

private theorem f400desc14_left_columns1 :
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 8=f400desc14IntegerLeftProduct 0 8) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 9=f400desc14IntegerLeftProduct 0 9) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 10=f400desc14IntegerLeftProduct 0 10) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 11=f400desc14IntegerLeftProduct 0 11) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 12=f400desc14IntegerLeftProduct 0 12) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 13=f400desc14IntegerLeftProduct 0 13) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 14=f400desc14IntegerLeftProduct 0 14) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 15=f400desc14IntegerLeftProduct 0 15) := by
  decide +kernel

#print axioms f400desc14_left_columns1

private theorem f400desc14_left_columns2 :
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 16=f400desc14IntegerLeftProduct 0 16) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 17=f400desc14IntegerLeftProduct 0 17) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 18=f400desc14IntegerLeftProduct 0 18) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 19=f400desc14IntegerLeftProduct 0 19) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 20=f400desc14IntegerLeftProduct 0 20) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 21=f400desc14IntegerLeftProduct 0 21) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 22=f400desc14IntegerLeftProduct 0 22) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 23=f400desc14IntegerLeftProduct 0 23) := by
  decide +kernel

#print axioms f400desc14_left_columns2

private theorem f400desc14_left_columns3 :
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 24=f400desc14IntegerLeftProduct 0 24) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 25=f400desc14IntegerLeftProduct 0 25) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 26=f400desc14IntegerLeftProduct 0 26) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 27=f400desc14IntegerLeftProduct 0 27) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 28=f400desc14IntegerLeftProduct 0 28) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 29=f400desc14IntegerLeftProduct 0 29) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 30=f400desc14IntegerLeftProduct 0 30) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 31=f400desc14IntegerLeftProduct 0 31) := by
  decide +kernel

#print axioms f400desc14_left_columns3

private theorem f400desc14_left_columns4 :
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 32=f400desc14IntegerLeftProduct 0 32) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 33=f400desc14IntegerLeftProduct 0 33) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 34=f400desc14IntegerLeftProduct 0 34) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 35=f400desc14IntegerLeftProduct 0 35) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 36=f400desc14IntegerLeftProduct 0 36) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 37=f400desc14IntegerLeftProduct 0 37) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 38=f400desc14IntegerLeftProduct 0 38) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 39=f400desc14IntegerLeftProduct 0 39) := by
  decide +kernel

#print axioms f400desc14_left_columns4

private theorem f400desc14_left_columns5 :
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 40=f400desc14IntegerLeftProduct 0 40) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 41=f400desc14IntegerLeftProduct 0 41) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 42=f400desc14IntegerLeftProduct 0 42) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 43=f400desc14IntegerLeftProduct 0 43) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 44=f400desc14IntegerLeftProduct 0 44) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 45=f400desc14IntegerLeftProduct 0 45) ∧
    ((f400desc14IntegerCoordinatesᵀ*f414rawInteger) 0 46=f400desc14IntegerLeftProduct 0 46) := by
  decide +kernel

#print axioms f400desc14_left_columns5

theorem f400desc14_compression_check :
    f400desc14ᵀ*f414rawM4Form*f400desc14=f400desc14Form := by
  have hD := f400desc14_coordinates_decode
  have hV : f400desc14IntegerCoordinatesᵀ*f414rawInteger=f400desc14IntegerLeftProduct := by
    ext a b
    fin_cases a
    fin_cases b
    · exact f400desc14_left_columns0.1
    · exact f400desc14_left_columns0.2.1
    · exact f400desc14_left_columns0.2.2.1
    · exact f400desc14_left_columns0.2.2.2.1
    · exact f400desc14_left_columns0.2.2.2.2.1
    · exact f400desc14_left_columns0.2.2.2.2.2.1
    · exact f400desc14_left_columns0.2.2.2.2.2.2.1
    · exact f400desc14_left_columns0.2.2.2.2.2.2.2
    · exact f400desc14_left_columns1.1
    · exact f400desc14_left_columns1.2.1
    · exact f400desc14_left_columns1.2.2.1
    · exact f400desc14_left_columns1.2.2.2.1
    · exact f400desc14_left_columns1.2.2.2.2.1
    · exact f400desc14_left_columns1.2.2.2.2.2.1
    · exact f400desc14_left_columns1.2.2.2.2.2.2.1
    · exact f400desc14_left_columns1.2.2.2.2.2.2.2
    · exact f400desc14_left_columns2.1
    · exact f400desc14_left_columns2.2.1
    · exact f400desc14_left_columns2.2.2.1
    · exact f400desc14_left_columns2.2.2.2.1
    · exact f400desc14_left_columns2.2.2.2.2.1
    · exact f400desc14_left_columns2.2.2.2.2.2.1
    · exact f400desc14_left_columns2.2.2.2.2.2.2.1
    · exact f400desc14_left_columns2.2.2.2.2.2.2.2
    · exact f400desc14_left_columns3.1
    · exact f400desc14_left_columns3.2.1
    · exact f400desc14_left_columns3.2.2.1
    · exact f400desc14_left_columns3.2.2.2.1
    · exact f400desc14_left_columns3.2.2.2.2.1
    · exact f400desc14_left_columns3.2.2.2.2.2.1
    · exact f400desc14_left_columns3.2.2.2.2.2.2.1
    · exact f400desc14_left_columns3.2.2.2.2.2.2.2
    · exact f400desc14_left_columns4.1
    · exact f400desc14_left_columns4.2.1
    · exact f400desc14_left_columns4.2.2.1
    · exact f400desc14_left_columns4.2.2.2.1
    · exact f400desc14_left_columns4.2.2.2.2.1
    · exact f400desc14_left_columns4.2.2.2.2.2.1
    · exact f400desc14_left_columns4.2.2.2.2.2.2.1
    · exact f400desc14_left_columns4.2.2.2.2.2.2.2
    · exact f400desc14_left_columns5.1
    · exact f400desc14_left_columns5.2.1
    · exact f400desc14_left_columns5.2.2.1
    · exact f400desc14_left_columns5.2.2.2.1
    · exact f400desc14_left_columns5.2.2.2.2.1
    · exact f400desc14_left_columns5.2.2.2.2.2.1
    · exact f400desc14_left_columns5.2.2.2.2.2.2
  have hY : f400desc14IntegerLeftProduct*f400desc14IntegerCoordinates=f400desc14IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc14IntegerLeftProduct*f400desc14IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc14IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc14IntegerForm=f400desc14Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc14IntegerForm) (f400desc14Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f414rawInteger f400desc14IntegerCoordinates f400desc14IntegerLeftProduct f400desc14IntegerForm
    f414rawM4Form f400desc14 f400desc14Form f414_raw_integer_check hD hV hY hF

theorem f400desc14_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[14] (natFourWordBlock f400basis (complexify b400relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[14]
          (natFourWordBlock f400basis (complexify b400relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f400desc14Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 14
    f400basis b400relative
    f414basis f400desc14 f414rawM4Form f400desc14Form
    f400desc14_actual f414_actual_raw_M4_matrix f400desc14_compression_check x y


#print axioms f400desc14_compression_check
#print axioms f400desc14_source_form
end TorusLean.BosonFiniteCertificate
