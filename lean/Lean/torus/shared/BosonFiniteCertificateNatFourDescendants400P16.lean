import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates400
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger416
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

def f400desc16Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(5503244681260994523358839002667/190734863281250)]

private def f400desc16IntegerCoordinates : Matrix (Fin 64) (Fin 1) ℤ :=
  !![4;
    192;
    1440;
    6720;
    21840;
    52416;
    96096;
    137280;
    77220;
    2880;
    40320;
    174720;
    524160;
    1153152;
    1921920;
    2471040;
    131040;
    1048320;
    2882880;
    5765760;
    8648640;
    4942080;
    1921920;
    9609600;
    17297280;
    23063040;
    10810800;
    34594560;
    20180160;
    24216192;
    13440;
    262080;
    1048320;
    2882880;
    5765760;
    8648640;
    4942080;
    1572480;
    11531520;
    28828800;
    51891840;
    69189120;
    19219200;
    86486400;
    138378240;
    80720640;
    86486400;
    242161920;
    48432384;
    2882880;
    28828800;
    64864800;
    103783680;
    60540480;
    86486400;
    345945600;
    484323840;
    302702400;
    363242880;
    76876800;
    403603200;
    242161920;
    605404800;
    63063000]

private def f400desc16IntegerLeftProduct : Matrix (Fin 1) (Fin 64) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, (-222407616550559746123729207296000), 0, 0, 0, 0, 0, 0, 23853216085440976264783676571648000, 0, 0, 0, 0, (-3534692358578253344234001727488000), 0, 0, 0, 849914784898942909152140918784000, 0, (-579848408355720819361770307584000), 0, 0, 0, 0, 0, 0, 0, 0, (-3296398498365261129861953028096000), 0, 0, 0, 0, 770483499839308393280924221440000, 0, 0, (-87374416507350729804195692544000), 0, 0, 0, 0, 0, 0, 0, (-405099561779977460047461089280000), 0, 0, 166805715128027145381330223104000, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def f400desc16IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![28852851474489642966627589830302760960000]

private theorem f400desc16_coordinates_decode : natFourIntegerMatrix 1 f400desc16IntegerCoordinates=f400desc16 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f400desc16IntegerCoordinates) (f400desc16) (by decide +kernel) a b

#print axioms f400desc16_coordinates_decode

private theorem f400desc16_left_columns0 :
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 0=f400desc16IntegerLeftProduct 0 0) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 1=f400desc16IntegerLeftProduct 0 1) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 2=f400desc16IntegerLeftProduct 0 2) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 3=f400desc16IntegerLeftProduct 0 3) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 4=f400desc16IntegerLeftProduct 0 4) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 5=f400desc16IntegerLeftProduct 0 5) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 6=f400desc16IntegerLeftProduct 0 6) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 7=f400desc16IntegerLeftProduct 0 7) := by
  decide +kernel

#print axioms f400desc16_left_columns0

private theorem f400desc16_left_columns1 :
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 8=f400desc16IntegerLeftProduct 0 8) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 9=f400desc16IntegerLeftProduct 0 9) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 10=f400desc16IntegerLeftProduct 0 10) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 11=f400desc16IntegerLeftProduct 0 11) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 12=f400desc16IntegerLeftProduct 0 12) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 13=f400desc16IntegerLeftProduct 0 13) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 14=f400desc16IntegerLeftProduct 0 14) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 15=f400desc16IntegerLeftProduct 0 15) := by
  decide +kernel

#print axioms f400desc16_left_columns1

private theorem f400desc16_left_columns2 :
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 16=f400desc16IntegerLeftProduct 0 16) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 17=f400desc16IntegerLeftProduct 0 17) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 18=f400desc16IntegerLeftProduct 0 18) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 19=f400desc16IntegerLeftProduct 0 19) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 20=f400desc16IntegerLeftProduct 0 20) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 21=f400desc16IntegerLeftProduct 0 21) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 22=f400desc16IntegerLeftProduct 0 22) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 23=f400desc16IntegerLeftProduct 0 23) := by
  decide +kernel

#print axioms f400desc16_left_columns2

private theorem f400desc16_left_columns3 :
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 24=f400desc16IntegerLeftProduct 0 24) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 25=f400desc16IntegerLeftProduct 0 25) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 26=f400desc16IntegerLeftProduct 0 26) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 27=f400desc16IntegerLeftProduct 0 27) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 28=f400desc16IntegerLeftProduct 0 28) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 29=f400desc16IntegerLeftProduct 0 29) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 30=f400desc16IntegerLeftProduct 0 30) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 31=f400desc16IntegerLeftProduct 0 31) := by
  decide +kernel

#print axioms f400desc16_left_columns3

private theorem f400desc16_left_columns4 :
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 32=f400desc16IntegerLeftProduct 0 32) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 33=f400desc16IntegerLeftProduct 0 33) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 34=f400desc16IntegerLeftProduct 0 34) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 35=f400desc16IntegerLeftProduct 0 35) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 36=f400desc16IntegerLeftProduct 0 36) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 37=f400desc16IntegerLeftProduct 0 37) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 38=f400desc16IntegerLeftProduct 0 38) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 39=f400desc16IntegerLeftProduct 0 39) := by
  decide +kernel

#print axioms f400desc16_left_columns4

private theorem f400desc16_left_columns5 :
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 40=f400desc16IntegerLeftProduct 0 40) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 41=f400desc16IntegerLeftProduct 0 41) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 42=f400desc16IntegerLeftProduct 0 42) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 43=f400desc16IntegerLeftProduct 0 43) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 44=f400desc16IntegerLeftProduct 0 44) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 45=f400desc16IntegerLeftProduct 0 45) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 46=f400desc16IntegerLeftProduct 0 46) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 47=f400desc16IntegerLeftProduct 0 47) := by
  decide +kernel

#print axioms f400desc16_left_columns5

private theorem f400desc16_left_columns6 :
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 48=f400desc16IntegerLeftProduct 0 48) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 49=f400desc16IntegerLeftProduct 0 49) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 50=f400desc16IntegerLeftProduct 0 50) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 51=f400desc16IntegerLeftProduct 0 51) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 52=f400desc16IntegerLeftProduct 0 52) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 53=f400desc16IntegerLeftProduct 0 53) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 54=f400desc16IntegerLeftProduct 0 54) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 55=f400desc16IntegerLeftProduct 0 55) := by
  decide +kernel

#print axioms f400desc16_left_columns6

private theorem f400desc16_left_columns7 :
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 56=f400desc16IntegerLeftProduct 0 56) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 57=f400desc16IntegerLeftProduct 0 57) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 58=f400desc16IntegerLeftProduct 0 58) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 59=f400desc16IntegerLeftProduct 0 59) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 60=f400desc16IntegerLeftProduct 0 60) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 61=f400desc16IntegerLeftProduct 0 61) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 62=f400desc16IntegerLeftProduct 0 62) ∧
    ((f400desc16IntegerCoordinatesᵀ*f416rawInteger) 0 63=f400desc16IntegerLeftProduct 0 63) := by
  decide +kernel

#print axioms f400desc16_left_columns7

theorem f400desc16_compression_check :
    f400desc16ᵀ*f416rawM4Form*f400desc16=f400desc16Form := by
  have hD := f400desc16_coordinates_decode
  have hV : f400desc16IntegerCoordinatesᵀ*f416rawInteger=f400desc16IntegerLeftProduct := by
    ext a b
    fin_cases a
    fin_cases b
    · exact f400desc16_left_columns0.1
    · exact f400desc16_left_columns0.2.1
    · exact f400desc16_left_columns0.2.2.1
    · exact f400desc16_left_columns0.2.2.2.1
    · exact f400desc16_left_columns0.2.2.2.2.1
    · exact f400desc16_left_columns0.2.2.2.2.2.1
    · exact f400desc16_left_columns0.2.2.2.2.2.2.1
    · exact f400desc16_left_columns0.2.2.2.2.2.2.2
    · exact f400desc16_left_columns1.1
    · exact f400desc16_left_columns1.2.1
    · exact f400desc16_left_columns1.2.2.1
    · exact f400desc16_left_columns1.2.2.2.1
    · exact f400desc16_left_columns1.2.2.2.2.1
    · exact f400desc16_left_columns1.2.2.2.2.2.1
    · exact f400desc16_left_columns1.2.2.2.2.2.2.1
    · exact f400desc16_left_columns1.2.2.2.2.2.2.2
    · exact f400desc16_left_columns2.1
    · exact f400desc16_left_columns2.2.1
    · exact f400desc16_left_columns2.2.2.1
    · exact f400desc16_left_columns2.2.2.2.1
    · exact f400desc16_left_columns2.2.2.2.2.1
    · exact f400desc16_left_columns2.2.2.2.2.2.1
    · exact f400desc16_left_columns2.2.2.2.2.2.2.1
    · exact f400desc16_left_columns2.2.2.2.2.2.2.2
    · exact f400desc16_left_columns3.1
    · exact f400desc16_left_columns3.2.1
    · exact f400desc16_left_columns3.2.2.1
    · exact f400desc16_left_columns3.2.2.2.1
    · exact f400desc16_left_columns3.2.2.2.2.1
    · exact f400desc16_left_columns3.2.2.2.2.2.1
    · exact f400desc16_left_columns3.2.2.2.2.2.2.1
    · exact f400desc16_left_columns3.2.2.2.2.2.2.2
    · exact f400desc16_left_columns4.1
    · exact f400desc16_left_columns4.2.1
    · exact f400desc16_left_columns4.2.2.1
    · exact f400desc16_left_columns4.2.2.2.1
    · exact f400desc16_left_columns4.2.2.2.2.1
    · exact f400desc16_left_columns4.2.2.2.2.2.1
    · exact f400desc16_left_columns4.2.2.2.2.2.2.1
    · exact f400desc16_left_columns4.2.2.2.2.2.2.2
    · exact f400desc16_left_columns5.1
    · exact f400desc16_left_columns5.2.1
    · exact f400desc16_left_columns5.2.2.1
    · exact f400desc16_left_columns5.2.2.2.1
    · exact f400desc16_left_columns5.2.2.2.2.1
    · exact f400desc16_left_columns5.2.2.2.2.2.1
    · exact f400desc16_left_columns5.2.2.2.2.2.2.1
    · exact f400desc16_left_columns5.2.2.2.2.2.2.2
    · exact f400desc16_left_columns6.1
    · exact f400desc16_left_columns6.2.1
    · exact f400desc16_left_columns6.2.2.1
    · exact f400desc16_left_columns6.2.2.2.1
    · exact f400desc16_left_columns6.2.2.2.2.1
    · exact f400desc16_left_columns6.2.2.2.2.2.1
    · exact f400desc16_left_columns6.2.2.2.2.2.2.1
    · exact f400desc16_left_columns6.2.2.2.2.2.2.2
    · exact f400desc16_left_columns7.1
    · exact f400desc16_left_columns7.2.1
    · exact f400desc16_left_columns7.2.2.1
    · exact f400desc16_left_columns7.2.2.2.1
    · exact f400desc16_left_columns7.2.2.2.2.1
    · exact f400desc16_left_columns7.2.2.2.2.2.1
    · exact f400desc16_left_columns7.2.2.2.2.2.2.1
    · exact f400desc16_left_columns7.2.2.2.2.2.2.2
  have hY : f400desc16IntegerLeftProduct*f400desc16IntegerCoordinates=f400desc16IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc16IntegerLeftProduct*f400desc16IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc16IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc16IntegerForm=f400desc16Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc16IntegerForm) (f400desc16Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f416rawInteger f400desc16IntegerCoordinates f400desc16IntegerLeftProduct f400desc16IntegerForm
    f416rawM4Form f400desc16 f400desc16Form f416_raw_integer_check hD hV hY hF

theorem f400desc16_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[16] (natFourWordBlock f400basis (complexify b400relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[16]
          (natFourWordBlock f400basis (complexify b400relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f400desc16Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 16
    f400basis b400relative
    f416basis f400desc16 f416rawM4Form f400desc16Form
    f400desc16_actual f416_actual_raw_M4_matrix f400desc16_compression_check x y


#print axioms f400desc16_compression_check
#print axioms f400desc16_source_form
end TorusLean.BosonFiniteCertificate
