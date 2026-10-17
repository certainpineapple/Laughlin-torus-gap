import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates403
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger416
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

def f403desc13Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(487925734325125589316565740999/305175781250000000)]

private def f403desc13IntegerCoordinates : Matrix (Fin 64) (Fin 1) ℤ :=
  !![1;
    36;
    192;
    588;
    1092;
    1092;
    0;
    (-1716);
    (-1287);
    396;
    3816;
    10296;
    15912;
    10296;
    (-10296);
    (-30888);
    8112;
    36816;
    41184;
    (-3432);
    (-82368);
    (-61776);
    30888;
    17160;
    (-133848);
    (-288288);
    (-77220);
    (-432432);
    (-288288);
    (-360360);
    1328;
    17316;
    41184;
    53196;
    20592;
    (-46332);
    (-41184);
    66456;
    267696;
    257400;
    (-30888);
    (-370656);
    205920;
    154440;
    (-494208);
    (-432432);
    (-257400);
    (-1297296);
    (-288288);
    75504;
    394680;
    308880;
    (-61776);
    (-144144);
    566280;
    617760;
    (-288288);
    0;
    (-216216);
    274560;
    720720;
    288288;
    1081080;
    150150]

private def f403desc13IntegerLeftProduct : Matrix (Fin 1) (Fin 64) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, 0, 3311212945026622084293132288000, 0, 0, 0, 0, 0, 0, (-355127576598431376937620937113600), 0, 0, 0, 0, 52624632537037806851149479936000, 0, 0, 0, (-12653563225822648384539200716800), 0, 8632804872778145356550219366400, 0, 0, 0, 0, 0, 0, 0, 0, 49076904599949449165878385049600, 0, 0, 0, 0, (-11470987271775662206198176153600), 0, 0, 1300833593248687124762315980800, 0, 0, 0, 0, 0, 0, 0, 6031137484384030988374435430400, 0, 0, (-2483409749192413421754492518400), 0, 0, 0, 0, 0, 0, 0, 0, 0]

private def f403desc13IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![6395340184946286124290090480422092800]

private theorem f403desc13_coordinates_decode : natFourIntegerMatrix 2 f403desc13IntegerCoordinates=f403desc13 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 2 f403desc13IntegerCoordinates) (f403desc13) (by decide +kernel) a b

#print axioms f403desc13_coordinates_decode

private theorem f403desc13_left_row0_columns0 :
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 0=f403desc13IntegerLeftProduct 0 0) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 1=f403desc13IntegerLeftProduct 0 1) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 2=f403desc13IntegerLeftProduct 0 2) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 3=f403desc13IntegerLeftProduct 0 3) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 4=f403desc13IntegerLeftProduct 0 4) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 5=f403desc13IntegerLeftProduct 0 5) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 6=f403desc13IntegerLeftProduct 0 6) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 7=f403desc13IntegerLeftProduct 0 7) := by
  decide +kernel

#print axioms f403desc13_left_row0_columns0

private theorem f403desc13_left_row0_columns1 :
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 8=f403desc13IntegerLeftProduct 0 8) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 9=f403desc13IntegerLeftProduct 0 9) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 10=f403desc13IntegerLeftProduct 0 10) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 11=f403desc13IntegerLeftProduct 0 11) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 12=f403desc13IntegerLeftProduct 0 12) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 13=f403desc13IntegerLeftProduct 0 13) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 14=f403desc13IntegerLeftProduct 0 14) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 15=f403desc13IntegerLeftProduct 0 15) := by
  decide +kernel

#print axioms f403desc13_left_row0_columns1

private theorem f403desc13_left_row0_columns2 :
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 16=f403desc13IntegerLeftProduct 0 16) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 17=f403desc13IntegerLeftProduct 0 17) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 18=f403desc13IntegerLeftProduct 0 18) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 19=f403desc13IntegerLeftProduct 0 19) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 20=f403desc13IntegerLeftProduct 0 20) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 21=f403desc13IntegerLeftProduct 0 21) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 22=f403desc13IntegerLeftProduct 0 22) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 23=f403desc13IntegerLeftProduct 0 23) := by
  decide +kernel

#print axioms f403desc13_left_row0_columns2

private theorem f403desc13_left_row0_columns3 :
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 24=f403desc13IntegerLeftProduct 0 24) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 25=f403desc13IntegerLeftProduct 0 25) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 26=f403desc13IntegerLeftProduct 0 26) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 27=f403desc13IntegerLeftProduct 0 27) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 28=f403desc13IntegerLeftProduct 0 28) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 29=f403desc13IntegerLeftProduct 0 29) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 30=f403desc13IntegerLeftProduct 0 30) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 31=f403desc13IntegerLeftProduct 0 31) := by
  decide +kernel

#print axioms f403desc13_left_row0_columns3

private theorem f403desc13_left_row0_columns4 :
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 32=f403desc13IntegerLeftProduct 0 32) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 33=f403desc13IntegerLeftProduct 0 33) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 34=f403desc13IntegerLeftProduct 0 34) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 35=f403desc13IntegerLeftProduct 0 35) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 36=f403desc13IntegerLeftProduct 0 36) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 37=f403desc13IntegerLeftProduct 0 37) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 38=f403desc13IntegerLeftProduct 0 38) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 39=f403desc13IntegerLeftProduct 0 39) := by
  decide +kernel

#print axioms f403desc13_left_row0_columns4

private theorem f403desc13_left_row0_columns5 :
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 40=f403desc13IntegerLeftProduct 0 40) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 41=f403desc13IntegerLeftProduct 0 41) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 42=f403desc13IntegerLeftProduct 0 42) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 43=f403desc13IntegerLeftProduct 0 43) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 44=f403desc13IntegerLeftProduct 0 44) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 45=f403desc13IntegerLeftProduct 0 45) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 46=f403desc13IntegerLeftProduct 0 46) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 47=f403desc13IntegerLeftProduct 0 47) := by
  decide +kernel

#print axioms f403desc13_left_row0_columns5

private theorem f403desc13_left_row0_columns6 :
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 48=f403desc13IntegerLeftProduct 0 48) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 49=f403desc13IntegerLeftProduct 0 49) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 50=f403desc13IntegerLeftProduct 0 50) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 51=f403desc13IntegerLeftProduct 0 51) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 52=f403desc13IntegerLeftProduct 0 52) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 53=f403desc13IntegerLeftProduct 0 53) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 54=f403desc13IntegerLeftProduct 0 54) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 55=f403desc13IntegerLeftProduct 0 55) := by
  decide +kernel

#print axioms f403desc13_left_row0_columns6

private theorem f403desc13_left_row0_columns7 :
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 56=f403desc13IntegerLeftProduct 0 56) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 57=f403desc13IntegerLeftProduct 0 57) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 58=f403desc13IntegerLeftProduct 0 58) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 59=f403desc13IntegerLeftProduct 0 59) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 60=f403desc13IntegerLeftProduct 0 60) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 61=f403desc13IntegerLeftProduct 0 61) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 62=f403desc13IntegerLeftProduct 0 62) ∧
    ((f403desc13IntegerCoordinatesᵀ*f416rawInteger) 0 63=f403desc13IntegerLeftProduct 0 63) := by
  decide +kernel

#print axioms f403desc13_left_row0_columns7

theorem f403desc13_compression_check :
    f403desc13ᵀ*f416rawM4Form*f403desc13=f403desc13Form := by
  have hD := f403desc13_coordinates_decode
  have hV : f403desc13IntegerCoordinatesᵀ*f416rawInteger=f403desc13IntegerLeftProduct := by
    ext a b
    fin_cases a
    · fin_cases b
      · exact f403desc13_left_row0_columns0.1
      · exact f403desc13_left_row0_columns0.2.1
      · exact f403desc13_left_row0_columns0.2.2.1
      · exact f403desc13_left_row0_columns0.2.2.2.1
      · exact f403desc13_left_row0_columns0.2.2.2.2.1
      · exact f403desc13_left_row0_columns0.2.2.2.2.2.1
      · exact f403desc13_left_row0_columns0.2.2.2.2.2.2.1
      · exact f403desc13_left_row0_columns0.2.2.2.2.2.2.2
      · exact f403desc13_left_row0_columns1.1
      · exact f403desc13_left_row0_columns1.2.1
      · exact f403desc13_left_row0_columns1.2.2.1
      · exact f403desc13_left_row0_columns1.2.2.2.1
      · exact f403desc13_left_row0_columns1.2.2.2.2.1
      · exact f403desc13_left_row0_columns1.2.2.2.2.2.1
      · exact f403desc13_left_row0_columns1.2.2.2.2.2.2.1
      · exact f403desc13_left_row0_columns1.2.2.2.2.2.2.2
      · exact f403desc13_left_row0_columns2.1
      · exact f403desc13_left_row0_columns2.2.1
      · exact f403desc13_left_row0_columns2.2.2.1
      · exact f403desc13_left_row0_columns2.2.2.2.1
      · exact f403desc13_left_row0_columns2.2.2.2.2.1
      · exact f403desc13_left_row0_columns2.2.2.2.2.2.1
      · exact f403desc13_left_row0_columns2.2.2.2.2.2.2.1
      · exact f403desc13_left_row0_columns2.2.2.2.2.2.2.2
      · exact f403desc13_left_row0_columns3.1
      · exact f403desc13_left_row0_columns3.2.1
      · exact f403desc13_left_row0_columns3.2.2.1
      · exact f403desc13_left_row0_columns3.2.2.2.1
      · exact f403desc13_left_row0_columns3.2.2.2.2.1
      · exact f403desc13_left_row0_columns3.2.2.2.2.2.1
      · exact f403desc13_left_row0_columns3.2.2.2.2.2.2.1
      · exact f403desc13_left_row0_columns3.2.2.2.2.2.2.2
      · exact f403desc13_left_row0_columns4.1
      · exact f403desc13_left_row0_columns4.2.1
      · exact f403desc13_left_row0_columns4.2.2.1
      · exact f403desc13_left_row0_columns4.2.2.2.1
      · exact f403desc13_left_row0_columns4.2.2.2.2.1
      · exact f403desc13_left_row0_columns4.2.2.2.2.2.1
      · exact f403desc13_left_row0_columns4.2.2.2.2.2.2.1
      · exact f403desc13_left_row0_columns4.2.2.2.2.2.2.2
      · exact f403desc13_left_row0_columns5.1
      · exact f403desc13_left_row0_columns5.2.1
      · exact f403desc13_left_row0_columns5.2.2.1
      · exact f403desc13_left_row0_columns5.2.2.2.1
      · exact f403desc13_left_row0_columns5.2.2.2.2.1
      · exact f403desc13_left_row0_columns5.2.2.2.2.2.1
      · exact f403desc13_left_row0_columns5.2.2.2.2.2.2.1
      · exact f403desc13_left_row0_columns5.2.2.2.2.2.2.2
      · exact f403desc13_left_row0_columns6.1
      · exact f403desc13_left_row0_columns6.2.1
      · exact f403desc13_left_row0_columns6.2.2.1
      · exact f403desc13_left_row0_columns6.2.2.2.1
      · exact f403desc13_left_row0_columns6.2.2.2.2.1
      · exact f403desc13_left_row0_columns6.2.2.2.2.2.1
      · exact f403desc13_left_row0_columns6.2.2.2.2.2.2.1
      · exact f403desc13_left_row0_columns6.2.2.2.2.2.2.2
      · exact f403desc13_left_row0_columns7.1
      · exact f403desc13_left_row0_columns7.2.1
      · exact f403desc13_left_row0_columns7.2.2.1
      · exact f403desc13_left_row0_columns7.2.2.2.1
      · exact f403desc13_left_row0_columns7.2.2.2.2.1
      · exact f403desc13_left_row0_columns7.2.2.2.2.2.1
      · exact f403desc13_left_row0_columns7.2.2.2.2.2.2.1
      · exact f403desc13_left_row0_columns7.2.2.2.2.2.2.2
  have hY : f403desc13IntegerLeftProduct*f403desc13IntegerCoordinates=f403desc13IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc13IntegerLeftProduct*f403desc13IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc13IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc13IntegerForm=f403desc13Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc13IntegerForm) (f403desc13Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 2
    f416rawInteger f403desc13IntegerCoordinates f403desc13IntegerLeftProduct f403desc13IntegerForm
    f416rawM4Form f403desc13 f403desc13Form f416_raw_integer_check hD hV hY hF

theorem f403desc13_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[13] (natFourWordBlock f403basis (complexify b403relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[13]
          (natFourWordBlock f403basis (complexify b403relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f403desc13Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 13
    f403basis b403relative
    f416basis f403desc13 f416rawM4Form f403desc13Form
    f403desc13_actual f416_actual_raw_M4_matrix f403desc13_compression_check x y


#print axioms f403desc13_compression_check
#print axioms f403desc13_source_form
end TorusLean.BosonFiniteCertificate
