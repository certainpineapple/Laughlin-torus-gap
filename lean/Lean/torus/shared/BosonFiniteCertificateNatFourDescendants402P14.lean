import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates402
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger416
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
import torus.shared.BosonFiniteCertificate402

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

def f402desc14Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(8390809186348161815345134510479/76293945312500000)]

private def f402desc14IntegerCoordinates : Matrix (Fin 64) (Fin 1) ℤ :=
  !![(-1);
    (-40);
    (-248);
    (-952);
    (-2548);
    (-5096);
    (-8008);
    (-10296);
    (-5577);
    (-488);
    (-5488);
    (-18928);
    (-45136);
    (-80080);
    (-112112);
    (-130416);
    (-13832);
    (-84448);
    (-176176);
    (-272272);
    (-336336);
    (-178464);
    (-112112);
    (-400400);
    (-528528);
    (-576576);
    (-300300);
    (-672672);
    (-336336);
    (-336336);
    (-1792);
    (-26936);
    (-81536);
    (-168168);
    (-256256);
    (-312312);
    (-164736);
    (-117936);
    (-608608);
    (-1041040);
    (-1297296);
    (-1345344);
    (-640640);
    (-1681680);
    (-1537536);
    (-672672);
    (-720720);
    (-672672);
    0;
    (-144144);
    (-880880);
    (-1081080);
    (-864864);
    (-336336);
    (-1201200);
    (-960960);
    1345344;
    1681680;
    3027024;
    0;
    3363360;
    2690688;
    8408400;
    1051050]

private def f402desc14IntegerLeftProduct : Matrix (Fin 1) (Fin 64) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 13731316310739223706134354329600, 0, 0, 0, 0, 0, 0, (-1472683625576974897799728516300800), 0, 0, 0, 0, 218229841178836642167740330803200, 0, 0, 0, (-52473242282008478677525197619200), 0, 35799501972547324798894640332800, 0, 0, 0, 0, 0, 0, 0, 0, 203517717465447994260383494963200, 0, 0, 0, 0, (-47569201147812590351903224627200), 0, 0, 5394445429237768870096306176000, 0, 0, 0, 0, 0, 0, 0, 25010610276822305103075115008000, 0, 0, (-10298487400683139151345192140800), 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def f402desc14IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![109980014167302626546091747055750348800]

private theorem f402desc14_coordinates_decode : natFourIntegerMatrix 1 f402desc14IntegerCoordinates=f402desc14 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f402desc14IntegerCoordinates) (f402desc14) (by decide +kernel) a b

#print axioms f402desc14_coordinates_decode

private theorem f402desc14_left_row0_columns0 :
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 0=f402desc14IntegerLeftProduct 0 0) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 1=f402desc14IntegerLeftProduct 0 1) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 2=f402desc14IntegerLeftProduct 0 2) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 3=f402desc14IntegerLeftProduct 0 3) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 4=f402desc14IntegerLeftProduct 0 4) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 5=f402desc14IntegerLeftProduct 0 5) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 6=f402desc14IntegerLeftProduct 0 6) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 7=f402desc14IntegerLeftProduct 0 7) := by
  decide +kernel

#print axioms f402desc14_left_row0_columns0

private theorem f402desc14_left_row0_columns1 :
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 8=f402desc14IntegerLeftProduct 0 8) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 9=f402desc14IntegerLeftProduct 0 9) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 10=f402desc14IntegerLeftProduct 0 10) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 11=f402desc14IntegerLeftProduct 0 11) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 12=f402desc14IntegerLeftProduct 0 12) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 13=f402desc14IntegerLeftProduct 0 13) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 14=f402desc14IntegerLeftProduct 0 14) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 15=f402desc14IntegerLeftProduct 0 15) := by
  decide +kernel

#print axioms f402desc14_left_row0_columns1

private theorem f402desc14_left_row0_columns2 :
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 16=f402desc14IntegerLeftProduct 0 16) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 17=f402desc14IntegerLeftProduct 0 17) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 18=f402desc14IntegerLeftProduct 0 18) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 19=f402desc14IntegerLeftProduct 0 19) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 20=f402desc14IntegerLeftProduct 0 20) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 21=f402desc14IntegerLeftProduct 0 21) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 22=f402desc14IntegerLeftProduct 0 22) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 23=f402desc14IntegerLeftProduct 0 23) := by
  decide +kernel

#print axioms f402desc14_left_row0_columns2

private theorem f402desc14_left_row0_columns3 :
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 24=f402desc14IntegerLeftProduct 0 24) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 25=f402desc14IntegerLeftProduct 0 25) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 26=f402desc14IntegerLeftProduct 0 26) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 27=f402desc14IntegerLeftProduct 0 27) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 28=f402desc14IntegerLeftProduct 0 28) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 29=f402desc14IntegerLeftProduct 0 29) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 30=f402desc14IntegerLeftProduct 0 30) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 31=f402desc14IntegerLeftProduct 0 31) := by
  decide +kernel

#print axioms f402desc14_left_row0_columns3

private theorem f402desc14_left_row0_columns4 :
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 32=f402desc14IntegerLeftProduct 0 32) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 33=f402desc14IntegerLeftProduct 0 33) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 34=f402desc14IntegerLeftProduct 0 34) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 35=f402desc14IntegerLeftProduct 0 35) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 36=f402desc14IntegerLeftProduct 0 36) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 37=f402desc14IntegerLeftProduct 0 37) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 38=f402desc14IntegerLeftProduct 0 38) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 39=f402desc14IntegerLeftProduct 0 39) := by
  decide +kernel

#print axioms f402desc14_left_row0_columns4

private theorem f402desc14_left_row0_columns5 :
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 40=f402desc14IntegerLeftProduct 0 40) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 41=f402desc14IntegerLeftProduct 0 41) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 42=f402desc14IntegerLeftProduct 0 42) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 43=f402desc14IntegerLeftProduct 0 43) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 44=f402desc14IntegerLeftProduct 0 44) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 45=f402desc14IntegerLeftProduct 0 45) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 46=f402desc14IntegerLeftProduct 0 46) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 47=f402desc14IntegerLeftProduct 0 47) := by
  decide +kernel

#print axioms f402desc14_left_row0_columns5

private theorem f402desc14_left_row0_columns6 :
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 48=f402desc14IntegerLeftProduct 0 48) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 49=f402desc14IntegerLeftProduct 0 49) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 50=f402desc14IntegerLeftProduct 0 50) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 51=f402desc14IntegerLeftProduct 0 51) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 52=f402desc14IntegerLeftProduct 0 52) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 53=f402desc14IntegerLeftProduct 0 53) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 54=f402desc14IntegerLeftProduct 0 54) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 55=f402desc14IntegerLeftProduct 0 55) := by
  decide +kernel

#print axioms f402desc14_left_row0_columns6

private theorem f402desc14_left_row0_columns7 :
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 56=f402desc14IntegerLeftProduct 0 56) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 57=f402desc14IntegerLeftProduct 0 57) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 58=f402desc14IntegerLeftProduct 0 58) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 59=f402desc14IntegerLeftProduct 0 59) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 60=f402desc14IntegerLeftProduct 0 60) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 61=f402desc14IntegerLeftProduct 0 61) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 62=f402desc14IntegerLeftProduct 0 62) ∧
    ((f402desc14IntegerCoordinatesᵀ*f416rawInteger) 0 63=f402desc14IntegerLeftProduct 0 63) := by
  decide +kernel

#print axioms f402desc14_left_row0_columns7

theorem f402desc14_compression_check :
    f402desc14ᵀ*f416rawM4Form*f402desc14=f402desc14Form := by
  have hD := f402desc14_coordinates_decode
  have hV : f402desc14IntegerCoordinatesᵀ*f416rawInteger=f402desc14IntegerLeftProduct := by
    ext a b
    fin_cases a
    · fin_cases b
      · exact f402desc14_left_row0_columns0.1
      · exact f402desc14_left_row0_columns0.2.1
      · exact f402desc14_left_row0_columns0.2.2.1
      · exact f402desc14_left_row0_columns0.2.2.2.1
      · exact f402desc14_left_row0_columns0.2.2.2.2.1
      · exact f402desc14_left_row0_columns0.2.2.2.2.2.1
      · exact f402desc14_left_row0_columns0.2.2.2.2.2.2.1
      · exact f402desc14_left_row0_columns0.2.2.2.2.2.2.2
      · exact f402desc14_left_row0_columns1.1
      · exact f402desc14_left_row0_columns1.2.1
      · exact f402desc14_left_row0_columns1.2.2.1
      · exact f402desc14_left_row0_columns1.2.2.2.1
      · exact f402desc14_left_row0_columns1.2.2.2.2.1
      · exact f402desc14_left_row0_columns1.2.2.2.2.2.1
      · exact f402desc14_left_row0_columns1.2.2.2.2.2.2.1
      · exact f402desc14_left_row0_columns1.2.2.2.2.2.2.2
      · exact f402desc14_left_row0_columns2.1
      · exact f402desc14_left_row0_columns2.2.1
      · exact f402desc14_left_row0_columns2.2.2.1
      · exact f402desc14_left_row0_columns2.2.2.2.1
      · exact f402desc14_left_row0_columns2.2.2.2.2.1
      · exact f402desc14_left_row0_columns2.2.2.2.2.2.1
      · exact f402desc14_left_row0_columns2.2.2.2.2.2.2.1
      · exact f402desc14_left_row0_columns2.2.2.2.2.2.2.2
      · exact f402desc14_left_row0_columns3.1
      · exact f402desc14_left_row0_columns3.2.1
      · exact f402desc14_left_row0_columns3.2.2.1
      · exact f402desc14_left_row0_columns3.2.2.2.1
      · exact f402desc14_left_row0_columns3.2.2.2.2.1
      · exact f402desc14_left_row0_columns3.2.2.2.2.2.1
      · exact f402desc14_left_row0_columns3.2.2.2.2.2.2.1
      · exact f402desc14_left_row0_columns3.2.2.2.2.2.2.2
      · exact f402desc14_left_row0_columns4.1
      · exact f402desc14_left_row0_columns4.2.1
      · exact f402desc14_left_row0_columns4.2.2.1
      · exact f402desc14_left_row0_columns4.2.2.2.1
      · exact f402desc14_left_row0_columns4.2.2.2.2.1
      · exact f402desc14_left_row0_columns4.2.2.2.2.2.1
      · exact f402desc14_left_row0_columns4.2.2.2.2.2.2.1
      · exact f402desc14_left_row0_columns4.2.2.2.2.2.2.2
      · exact f402desc14_left_row0_columns5.1
      · exact f402desc14_left_row0_columns5.2.1
      · exact f402desc14_left_row0_columns5.2.2.1
      · exact f402desc14_left_row0_columns5.2.2.2.1
      · exact f402desc14_left_row0_columns5.2.2.2.2.1
      · exact f402desc14_left_row0_columns5.2.2.2.2.2.1
      · exact f402desc14_left_row0_columns5.2.2.2.2.2.2.1
      · exact f402desc14_left_row0_columns5.2.2.2.2.2.2.2
      · exact f402desc14_left_row0_columns6.1
      · exact f402desc14_left_row0_columns6.2.1
      · exact f402desc14_left_row0_columns6.2.2.1
      · exact f402desc14_left_row0_columns6.2.2.2.1
      · exact f402desc14_left_row0_columns6.2.2.2.2.1
      · exact f402desc14_left_row0_columns6.2.2.2.2.2.1
      · exact f402desc14_left_row0_columns6.2.2.2.2.2.2.1
      · exact f402desc14_left_row0_columns6.2.2.2.2.2.2.2
      · exact f402desc14_left_row0_columns7.1
      · exact f402desc14_left_row0_columns7.2.1
      · exact f402desc14_left_row0_columns7.2.2.1
      · exact f402desc14_left_row0_columns7.2.2.2.1
      · exact f402desc14_left_row0_columns7.2.2.2.2.1
      · exact f402desc14_left_row0_columns7.2.2.2.2.2.1
      · exact f402desc14_left_row0_columns7.2.2.2.2.2.2.1
      · exact f402desc14_left_row0_columns7.2.2.2.2.2.2.2
  have hY : f402desc14IntegerLeftProduct*f402desc14IntegerCoordinates=f402desc14IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc14IntegerLeftProduct*f402desc14IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc14IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc14IntegerForm=f402desc14Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc14IntegerForm) (f402desc14Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f416rawInteger f402desc14IntegerCoordinates f402desc14IntegerLeftProduct f402desc14IntegerForm
    f416rawM4Form f402desc14 f402desc14Form f416_raw_integer_check hD hV hY hF

theorem f402desc14_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[14] (natFourWordBlock f402basis (complexify b402relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[14]
          (natFourWordBlock f402basis (complexify b402relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f402desc14Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 14
    f402basis b402relative
    f416basis f402desc14 f416rawM4Form f402desc14Form
    f402desc14_actual f416_actual_raw_M4_matrix f402desc14_compression_check x y


#print axioms f402desc14_compression_check
#print axioms f402desc14_source_form
end TorusLean.BosonFiniteCertificate
