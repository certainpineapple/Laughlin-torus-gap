import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates402
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger415
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

def f402desc13Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(20858255463973940696187158633651673/39062500000000000000)]

private def f402desc13IntegerCoordinates : Matrix (Fin 54) (Fin 1) ℤ :=
  !![(-1);
    (-37);
    (-211);
    (-741);
    (-1807);
    (-3289);
    (-4719);
    (-5577);
    (-414);
    (-4238);
    (-13208);
    (-28314);
    (-45188);
    (-57486);
    (-30888);
    (-9594);
    (-52052);
    (-95810);
    (-131274);
    (-147576);
    (-60060);
    (-184470);
    (-212784);
    (-108108);
    (-115830);
    (-228228);
    (-36036);
    (-1378);
    (-18564);
    (-49764);
    (-90090);
    (-120978);
    (-133848);
    (-71214);
    (-314600);
    (-450450);
    (-473616);
    (-228228);
    (-265980);
    (-514800);
    (-336336);
    (-90090);
    36036;
    (-72930);
    (-347490);
    (-283140);
    (-108108);
    (-240240);
    600600;
    648648;
    1171170;
    240240;
    2042040;
    1051050]

private def f402desc13IntegerLeftProduct : Matrix (Fin 1) (Fin 54) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, (-21520815304124035318974683883955200), 0, 0, 0, 0, 0, (-246335071680278083434376385740800), (-7059800147851563549253026181171200), 0, 0, 0, 33841228901922324934912852992000, (-1048541611664675417246540866483200), 0, (-4368914499759125080770522316800), 238955850577513284605638440192000, 0, (-215015441960604181062076233523200), 0, 0, 0, 0, 0, 0, 41860248537357998344448461209600, (-924308047585025122361860354636800), 0, 0, (-15256957272159549762205905715200), 217037167122033274899261207628800, 0, 17855070192739816224938368819200, (-14582159183309099345734522752000), 0, 0, 0, 0, (-1051992215096281866032622796800), (-160734406718439403936792267161600), 0, 61617559514335687485926676172800, 0, 0, 0, 0, 0, 0]

private def f402desc13IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![533971339877732881822391261021482828800]

private theorem f402desc13_coordinates_decode : natFourIntegerMatrix 1 f402desc13IntegerCoordinates=f402desc13 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f402desc13IntegerCoordinates) (f402desc13) (by decide +kernel) a b

#print axioms f402desc13_coordinates_decode

private theorem f402desc13_left_row0_columns0 :
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 0=f402desc13IntegerLeftProduct 0 0) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 1=f402desc13IntegerLeftProduct 0 1) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 2=f402desc13IntegerLeftProduct 0 2) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 3=f402desc13IntegerLeftProduct 0 3) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 4=f402desc13IntegerLeftProduct 0 4) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 5=f402desc13IntegerLeftProduct 0 5) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 6=f402desc13IntegerLeftProduct 0 6) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 7=f402desc13IntegerLeftProduct 0 7) := by
  decide +kernel

#print axioms f402desc13_left_row0_columns0

private theorem f402desc13_left_row0_columns1 :
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 8=f402desc13IntegerLeftProduct 0 8) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 9=f402desc13IntegerLeftProduct 0 9) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 10=f402desc13IntegerLeftProduct 0 10) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 11=f402desc13IntegerLeftProduct 0 11) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 12=f402desc13IntegerLeftProduct 0 12) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 13=f402desc13IntegerLeftProduct 0 13) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 14=f402desc13IntegerLeftProduct 0 14) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 15=f402desc13IntegerLeftProduct 0 15) := by
  decide +kernel

#print axioms f402desc13_left_row0_columns1

private theorem f402desc13_left_row0_columns2 :
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 16=f402desc13IntegerLeftProduct 0 16) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 17=f402desc13IntegerLeftProduct 0 17) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 18=f402desc13IntegerLeftProduct 0 18) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 19=f402desc13IntegerLeftProduct 0 19) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 20=f402desc13IntegerLeftProduct 0 20) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 21=f402desc13IntegerLeftProduct 0 21) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 22=f402desc13IntegerLeftProduct 0 22) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 23=f402desc13IntegerLeftProduct 0 23) := by
  decide +kernel

#print axioms f402desc13_left_row0_columns2

private theorem f402desc13_left_row0_columns3 :
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 24=f402desc13IntegerLeftProduct 0 24) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 25=f402desc13IntegerLeftProduct 0 25) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 26=f402desc13IntegerLeftProduct 0 26) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 27=f402desc13IntegerLeftProduct 0 27) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 28=f402desc13IntegerLeftProduct 0 28) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 29=f402desc13IntegerLeftProduct 0 29) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 30=f402desc13IntegerLeftProduct 0 30) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 31=f402desc13IntegerLeftProduct 0 31) := by
  decide +kernel

#print axioms f402desc13_left_row0_columns3

private theorem f402desc13_left_row0_columns4 :
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 32=f402desc13IntegerLeftProduct 0 32) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 33=f402desc13IntegerLeftProduct 0 33) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 34=f402desc13IntegerLeftProduct 0 34) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 35=f402desc13IntegerLeftProduct 0 35) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 36=f402desc13IntegerLeftProduct 0 36) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 37=f402desc13IntegerLeftProduct 0 37) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 38=f402desc13IntegerLeftProduct 0 38) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 39=f402desc13IntegerLeftProduct 0 39) := by
  decide +kernel

#print axioms f402desc13_left_row0_columns4

private theorem f402desc13_left_row0_columns5 :
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 40=f402desc13IntegerLeftProduct 0 40) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 41=f402desc13IntegerLeftProduct 0 41) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 42=f402desc13IntegerLeftProduct 0 42) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 43=f402desc13IntegerLeftProduct 0 43) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 44=f402desc13IntegerLeftProduct 0 44) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 45=f402desc13IntegerLeftProduct 0 45) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 46=f402desc13IntegerLeftProduct 0 46) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 47=f402desc13IntegerLeftProduct 0 47) := by
  decide +kernel

#print axioms f402desc13_left_row0_columns5

private theorem f402desc13_left_row0_columns6 :
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 48=f402desc13IntegerLeftProduct 0 48) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 49=f402desc13IntegerLeftProduct 0 49) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 50=f402desc13IntegerLeftProduct 0 50) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 51=f402desc13IntegerLeftProduct 0 51) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 52=f402desc13IntegerLeftProduct 0 52) ∧
    ((f402desc13IntegerCoordinatesᵀ*f415rawInteger) 0 53=f402desc13IntegerLeftProduct 0 53) := by
  decide +kernel

#print axioms f402desc13_left_row0_columns6

theorem f402desc13_compression_check :
    f402desc13ᵀ*f415rawM4Form*f402desc13=f402desc13Form := by
  have hD := f402desc13_coordinates_decode
  have hV : f402desc13IntegerCoordinatesᵀ*f415rawInteger=f402desc13IntegerLeftProduct := by
    ext a b
    fin_cases a
    · fin_cases b
      · exact f402desc13_left_row0_columns0.1
      · exact f402desc13_left_row0_columns0.2.1
      · exact f402desc13_left_row0_columns0.2.2.1
      · exact f402desc13_left_row0_columns0.2.2.2.1
      · exact f402desc13_left_row0_columns0.2.2.2.2.1
      · exact f402desc13_left_row0_columns0.2.2.2.2.2.1
      · exact f402desc13_left_row0_columns0.2.2.2.2.2.2.1
      · exact f402desc13_left_row0_columns0.2.2.2.2.2.2.2
      · exact f402desc13_left_row0_columns1.1
      · exact f402desc13_left_row0_columns1.2.1
      · exact f402desc13_left_row0_columns1.2.2.1
      · exact f402desc13_left_row0_columns1.2.2.2.1
      · exact f402desc13_left_row0_columns1.2.2.2.2.1
      · exact f402desc13_left_row0_columns1.2.2.2.2.2.1
      · exact f402desc13_left_row0_columns1.2.2.2.2.2.2.1
      · exact f402desc13_left_row0_columns1.2.2.2.2.2.2.2
      · exact f402desc13_left_row0_columns2.1
      · exact f402desc13_left_row0_columns2.2.1
      · exact f402desc13_left_row0_columns2.2.2.1
      · exact f402desc13_left_row0_columns2.2.2.2.1
      · exact f402desc13_left_row0_columns2.2.2.2.2.1
      · exact f402desc13_left_row0_columns2.2.2.2.2.2.1
      · exact f402desc13_left_row0_columns2.2.2.2.2.2.2.1
      · exact f402desc13_left_row0_columns2.2.2.2.2.2.2.2
      · exact f402desc13_left_row0_columns3.1
      · exact f402desc13_left_row0_columns3.2.1
      · exact f402desc13_left_row0_columns3.2.2.1
      · exact f402desc13_left_row0_columns3.2.2.2.1
      · exact f402desc13_left_row0_columns3.2.2.2.2.1
      · exact f402desc13_left_row0_columns3.2.2.2.2.2.1
      · exact f402desc13_left_row0_columns3.2.2.2.2.2.2.1
      · exact f402desc13_left_row0_columns3.2.2.2.2.2.2.2
      · exact f402desc13_left_row0_columns4.1
      · exact f402desc13_left_row0_columns4.2.1
      · exact f402desc13_left_row0_columns4.2.2.1
      · exact f402desc13_left_row0_columns4.2.2.2.1
      · exact f402desc13_left_row0_columns4.2.2.2.2.1
      · exact f402desc13_left_row0_columns4.2.2.2.2.2.1
      · exact f402desc13_left_row0_columns4.2.2.2.2.2.2.1
      · exact f402desc13_left_row0_columns4.2.2.2.2.2.2.2
      · exact f402desc13_left_row0_columns5.1
      · exact f402desc13_left_row0_columns5.2.1
      · exact f402desc13_left_row0_columns5.2.2.1
      · exact f402desc13_left_row0_columns5.2.2.2.1
      · exact f402desc13_left_row0_columns5.2.2.2.2.1
      · exact f402desc13_left_row0_columns5.2.2.2.2.2.1
      · exact f402desc13_left_row0_columns5.2.2.2.2.2.2.1
      · exact f402desc13_left_row0_columns5.2.2.2.2.2.2.2
      · exact f402desc13_left_row0_columns6.1
      · exact f402desc13_left_row0_columns6.2.1
      · exact f402desc13_left_row0_columns6.2.2.1
      · exact f402desc13_left_row0_columns6.2.2.2.1
      · exact f402desc13_left_row0_columns6.2.2.2.2.1
      · exact f402desc13_left_row0_columns6.2.2.2.2.2
  have hY : f402desc13IntegerLeftProduct*f402desc13IntegerCoordinates=f402desc13IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc13IntegerLeftProduct*f402desc13IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc13IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc13IntegerForm=f402desc13Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc13IntegerForm) (f402desc13Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f415rawInteger f402desc13IntegerCoordinates f402desc13IntegerLeftProduct f402desc13IntegerForm
    f415rawM4Form f402desc13 f402desc13Form f415_raw_integer_check hD hV hY hF

theorem f402desc13_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[13] (natFourWordBlock f402basis (complexify b402relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[13]
          (natFourWordBlock f402basis (complexify b402relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f402desc13Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 13
    f402basis b402relative
    f415basis f402desc13 f415rawM4Form f402desc13Form
    f402desc13_actual f415_actual_raw_M4_matrix f402desc13_compression_check x y


#print axioms f402desc13_compression_check
#print axioms f402desc13_source_form
end TorusLean.BosonFiniteCertificate
