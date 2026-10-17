import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates400
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger415
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

def f400desc15Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(28497370679125000129467642979135809/97656250000000000)]

private def f400desc15IntegerCoordinates : Matrix (Fin 54) (Fin 1) ℤ :=
  !![4;
    180;
    1260;
    5460;
    16380;
    36036;
    60060;
    77220;
    2520;
    32760;
    131040;
    360360;
    720720;
    1081080;
    617760;
    98280;
    720720;
    1801800;
    3243240;
    4324320;
    1201200;
    5405400;
    8648640;
    5045040;
    5405400;
    15135120;
    3027024;
    10920;
    196560;
    720720;
    1801800;
    3243240;
    4324320;
    1081080;
    7207200;
    16216200;
    25945920;
    15135120;
    10810800;
    43243200;
    60540480;
    37837800;
    45405360;
    1801800;
    16216200;
    32432400;
    45405360;
    43243200;
    151351200;
    90810720;
    113513400;
    33633600;
    151351200;
    63063000]

private def f400desc15IntegerLeftProduct : Matrix (Fin 1) (Fin 54) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, 413050888666313212327757898177024000, 0, 0, 0, 0, 0, 4089100703715451764179725197312000, 133919340612773244466528461911040000, 0, 0, 0, (-561755903694694847536848113664000), 22170771846295528686017350058496000, 0, 72522875106724353359838806016000, (-4628300581426859472153162912768000), 0, 4816787449316399035062928920576000, 0, 0, 0, 0, 0, 0, (-694869601698820490580189167616000), 19618766947750898882710119716352000, 0, 0, 253261682321987250605919633408000, (-4120589827045136163382847479296000), 0, (-296389686563485035901617549312000), 703985892739970909074524790272000, 0, 0, 0, 0, 17462818655903504387804332032000, 3763701545666324021152070565888000, 0, (-856810765291827413606648997888000), 0, 0, 0, 0, 0, 0]

private def f400desc15IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![291813075754240001325748664106350684160000]

private theorem f400desc15_coordinates_decode : natFourIntegerMatrix 1 f400desc15IntegerCoordinates=f400desc15 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f400desc15IntegerCoordinates) (f400desc15) (by decide +kernel) a b

#print axioms f400desc15_coordinates_decode

private theorem f400desc15_left_columns0 :
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 0=f400desc15IntegerLeftProduct 0 0) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 1=f400desc15IntegerLeftProduct 0 1) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 2=f400desc15IntegerLeftProduct 0 2) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 3=f400desc15IntegerLeftProduct 0 3) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 4=f400desc15IntegerLeftProduct 0 4) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 5=f400desc15IntegerLeftProduct 0 5) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 6=f400desc15IntegerLeftProduct 0 6) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 7=f400desc15IntegerLeftProduct 0 7) := by
  decide +kernel

#print axioms f400desc15_left_columns0

private theorem f400desc15_left_columns1 :
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 8=f400desc15IntegerLeftProduct 0 8) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 9=f400desc15IntegerLeftProduct 0 9) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 10=f400desc15IntegerLeftProduct 0 10) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 11=f400desc15IntegerLeftProduct 0 11) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 12=f400desc15IntegerLeftProduct 0 12) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 13=f400desc15IntegerLeftProduct 0 13) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 14=f400desc15IntegerLeftProduct 0 14) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 15=f400desc15IntegerLeftProduct 0 15) := by
  decide +kernel

#print axioms f400desc15_left_columns1

private theorem f400desc15_left_columns2 :
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 16=f400desc15IntegerLeftProduct 0 16) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 17=f400desc15IntegerLeftProduct 0 17) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 18=f400desc15IntegerLeftProduct 0 18) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 19=f400desc15IntegerLeftProduct 0 19) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 20=f400desc15IntegerLeftProduct 0 20) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 21=f400desc15IntegerLeftProduct 0 21) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 22=f400desc15IntegerLeftProduct 0 22) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 23=f400desc15IntegerLeftProduct 0 23) := by
  decide +kernel

#print axioms f400desc15_left_columns2

private theorem f400desc15_left_columns3 :
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 24=f400desc15IntegerLeftProduct 0 24) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 25=f400desc15IntegerLeftProduct 0 25) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 26=f400desc15IntegerLeftProduct 0 26) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 27=f400desc15IntegerLeftProduct 0 27) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 28=f400desc15IntegerLeftProduct 0 28) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 29=f400desc15IntegerLeftProduct 0 29) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 30=f400desc15IntegerLeftProduct 0 30) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 31=f400desc15IntegerLeftProduct 0 31) := by
  decide +kernel

#print axioms f400desc15_left_columns3

private theorem f400desc15_left_columns4 :
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 32=f400desc15IntegerLeftProduct 0 32) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 33=f400desc15IntegerLeftProduct 0 33) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 34=f400desc15IntegerLeftProduct 0 34) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 35=f400desc15IntegerLeftProduct 0 35) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 36=f400desc15IntegerLeftProduct 0 36) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 37=f400desc15IntegerLeftProduct 0 37) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 38=f400desc15IntegerLeftProduct 0 38) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 39=f400desc15IntegerLeftProduct 0 39) := by
  decide +kernel

#print axioms f400desc15_left_columns4

private theorem f400desc15_left_columns5 :
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 40=f400desc15IntegerLeftProduct 0 40) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 41=f400desc15IntegerLeftProduct 0 41) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 42=f400desc15IntegerLeftProduct 0 42) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 43=f400desc15IntegerLeftProduct 0 43) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 44=f400desc15IntegerLeftProduct 0 44) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 45=f400desc15IntegerLeftProduct 0 45) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 46=f400desc15IntegerLeftProduct 0 46) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 47=f400desc15IntegerLeftProduct 0 47) := by
  decide +kernel

#print axioms f400desc15_left_columns5

private theorem f400desc15_left_columns6 :
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 48=f400desc15IntegerLeftProduct 0 48) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 49=f400desc15IntegerLeftProduct 0 49) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 50=f400desc15IntegerLeftProduct 0 50) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 51=f400desc15IntegerLeftProduct 0 51) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 52=f400desc15IntegerLeftProduct 0 52) ∧
    ((f400desc15IntegerCoordinatesᵀ*f415rawInteger) 0 53=f400desc15IntegerLeftProduct 0 53) := by
  decide +kernel

#print axioms f400desc15_left_columns6

theorem f400desc15_compression_check :
    f400desc15ᵀ*f415rawM4Form*f400desc15=f400desc15Form := by
  have hD := f400desc15_coordinates_decode
  have hV : f400desc15IntegerCoordinatesᵀ*f415rawInteger=f400desc15IntegerLeftProduct := by
    ext a b
    fin_cases a
    fin_cases b
    · exact f400desc15_left_columns0.1
    · exact f400desc15_left_columns0.2.1
    · exact f400desc15_left_columns0.2.2.1
    · exact f400desc15_left_columns0.2.2.2.1
    · exact f400desc15_left_columns0.2.2.2.2.1
    · exact f400desc15_left_columns0.2.2.2.2.2.1
    · exact f400desc15_left_columns0.2.2.2.2.2.2.1
    · exact f400desc15_left_columns0.2.2.2.2.2.2.2
    · exact f400desc15_left_columns1.1
    · exact f400desc15_left_columns1.2.1
    · exact f400desc15_left_columns1.2.2.1
    · exact f400desc15_left_columns1.2.2.2.1
    · exact f400desc15_left_columns1.2.2.2.2.1
    · exact f400desc15_left_columns1.2.2.2.2.2.1
    · exact f400desc15_left_columns1.2.2.2.2.2.2.1
    · exact f400desc15_left_columns1.2.2.2.2.2.2.2
    · exact f400desc15_left_columns2.1
    · exact f400desc15_left_columns2.2.1
    · exact f400desc15_left_columns2.2.2.1
    · exact f400desc15_left_columns2.2.2.2.1
    · exact f400desc15_left_columns2.2.2.2.2.1
    · exact f400desc15_left_columns2.2.2.2.2.2.1
    · exact f400desc15_left_columns2.2.2.2.2.2.2.1
    · exact f400desc15_left_columns2.2.2.2.2.2.2.2
    · exact f400desc15_left_columns3.1
    · exact f400desc15_left_columns3.2.1
    · exact f400desc15_left_columns3.2.2.1
    · exact f400desc15_left_columns3.2.2.2.1
    · exact f400desc15_left_columns3.2.2.2.2.1
    · exact f400desc15_left_columns3.2.2.2.2.2.1
    · exact f400desc15_left_columns3.2.2.2.2.2.2.1
    · exact f400desc15_left_columns3.2.2.2.2.2.2.2
    · exact f400desc15_left_columns4.1
    · exact f400desc15_left_columns4.2.1
    · exact f400desc15_left_columns4.2.2.1
    · exact f400desc15_left_columns4.2.2.2.1
    · exact f400desc15_left_columns4.2.2.2.2.1
    · exact f400desc15_left_columns4.2.2.2.2.2.1
    · exact f400desc15_left_columns4.2.2.2.2.2.2.1
    · exact f400desc15_left_columns4.2.2.2.2.2.2.2
    · exact f400desc15_left_columns5.1
    · exact f400desc15_left_columns5.2.1
    · exact f400desc15_left_columns5.2.2.1
    · exact f400desc15_left_columns5.2.2.2.1
    · exact f400desc15_left_columns5.2.2.2.2.1
    · exact f400desc15_left_columns5.2.2.2.2.2.1
    · exact f400desc15_left_columns5.2.2.2.2.2.2.1
    · exact f400desc15_left_columns5.2.2.2.2.2.2.2
    · exact f400desc15_left_columns6.1
    · exact f400desc15_left_columns6.2.1
    · exact f400desc15_left_columns6.2.2.1
    · exact f400desc15_left_columns6.2.2.2.1
    · exact f400desc15_left_columns6.2.2.2.2.1
    · exact f400desc15_left_columns6.2.2.2.2.2
  have hY : f400desc15IntegerLeftProduct*f400desc15IntegerCoordinates=f400desc15IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc15IntegerLeftProduct*f400desc15IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f400desc15IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc15IntegerForm=f400desc15Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f400desc15IntegerForm) (f400desc15Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f415rawInteger f400desc15IntegerCoordinates f400desc15IntegerLeftProduct f400desc15IntegerForm
    f415rawM4Form f400desc15 f400desc15Form f415_raw_integer_check hD hV hY hF

theorem f400desc15_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[15] (natFourWordBlock f400basis (complexify b400relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[15]
          (natFourWordBlock f400basis (complexify b400relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f400desc15Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 15
    f400basis b400relative
    f415basis f400desc15 f415rawM4Form f400desc15Form
    f400desc15_actual f415_actual_raw_M4_matrix f400desc15_compression_check x y


#print axioms f400desc15_compression_check
#print axioms f400desc15_source_form
end TorusLean.BosonFiniteCertificate
