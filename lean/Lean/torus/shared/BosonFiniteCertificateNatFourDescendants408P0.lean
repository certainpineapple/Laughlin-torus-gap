import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates408
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger408
import torus.shared.BosonFiniteCertificateNatFourRaise408
import torus.shared.BosonFiniteCertificateNatFourRaise409
import torus.shared.BosonFiniteCertificateNatFourRaise410
import torus.shared.BosonFiniteCertificateNatFourRaise411
import torus.shared.BosonFiniteCertificateNatFourRaise412
import torus.shared.BosonFiniteCertificateNatFourRaise413
import torus.shared.BosonFiniteCertificateNatFourRaise414
import torus.shared.BosonFiniteCertificateNatFourRaise415
import torus.shared.BosonFiniteCertificate408

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

def f408desc0Form : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(-3716405440073408185344939/4882812500000000000000), (549210846184520782247172921/2187500000000000000000000), (278811940752233365880168439/10937500000000000000000000), (-137638276663401434380144101/683593750000000000000000);
    (549210846184520782247172921/2187500000000000000000000), (-35173376120649143565104463/437500000000000000000000), (-3299716724728730440145637201/43750000000000000000000000), (1357698695301910753915940581/10937500000000000000000000);
    (278811940752233365880168439/10937500000000000000000000), (-3299716724728730440145637201/43750000000000000000000000), (-1232424774952828832464576971/21875000000000000000000000), (1205649623507495329474962471/10937500000000000000000000);
    (-137638276663401434380144101/683593750000000000000000), (1357698695301910753915940581/10937500000000000000000000), (1205649623507495329474962471/10937500000000000000000000), (-14696548531776104313338941/68359375000000000000000)]

private def f408desc0IntegerCoordinates : Matrix (Fin 15) (Fin 4) ℤ :=
  !![6, (-6), (-6), 10;
    (-48), 48, 48, (-80);
    168, (-63), (-42), 56;
    (-336), 21, 21, 0;
    210, 0, 0, 0;
    0, (-105), (-126), 224;
    0, 315, 189, (-336);
    0, (-105), (-105), 0;
    0, (-315), 0, 140;
    0, 210, 0, 0;
    0, 0, 126, (-224);
    0, 0, (-315), 560;
    0, 0, 210, 0;
    0, 0, 0, (-560);
    0, 0, 0, 210]

private def f408desc0IntegerLeftProduct : Matrix (Fin 4) (Fin 15) ℤ :=
  !![13691375000824470044943052800, (-14060160763056608188826355840), (-52911909301876071345064699776), 49696519257497669627520194112, (-41596140087616506056818320384), 5573985296684980490587918080, 26193165755457521297120610816, 13318397742128980805706350592, (-2922882226719927550113051648), 1258069237978709408341065984, (-2562600981069621825367674240), 2916143177069547393986725632, (-14252395125835801589280401664), 3381711913723260140799971328, 2239286560126183511075930112;
    (-4387723436430376711398223200), (-13395263946720118327413450720), 32033187103711860215651878416, (-18202927331157497114615857152), (-4963403268745504743261398976), 3117852941790153103825998240, (-2815409669405780829288221136), (-5639080068279691458973474752), (-1070132284845115183007714592), (-1159258070448035560162846224), (-6254842639840142509106219520), (-1261440384923133519059570112), (-1229513595282933968981334816), (-1125998436754024714329730848), (-795984133697034433497122112);
    774050342262368857365708000, (-17869324692245851515352616640), 24482656261353057416515015056, 1070674698563863278098484960, (-16626389025515360662789106112), 2181060386643383416048223520, (-1487737445919951946593101616), (-2753689939566459729690128400), 2010610502926907185800129888, 466829073238351925648396304, (-5285323371935418441459192000), (-719453650031473692403952640), 427487251089842426254367232, (-321764273333607469662683568), (-848881479359805943321472832);
    (-2621196358497438473613657600), 31911183476948691138417828480, (-36482667885765556347886162560), 9117796927387685409939621312, 8861006920695448737802235904, (-5934984825259209155690737920), 3492904850027531504591166720, 4064172017687076616237967232, (-1264807592780675010877132800), (-1229616295929752658272765952), 15443501770459956680225118720, 3053071753875856361090226432, (-1787729300606552135749335552), 1175734652706186076250060160, 1091714132899825197476474880]

private def f408desc0IntegerForm : Matrix (Fin 4) (Fin 4) ℤ :=
  !![(-33565384685002199239416178667520), 11072090659079938970103006087360, 1124169745113004931228839146048, (-8879320504109353334731856243712);
    11072090659079938970103006087360, (-3545476312961433671362529870400), (-3326114458526560283666802298608), 5474241139457304159789072422592;
    1124169745113004931228839146048, (-3326114458526560283666802298608), (-2484568346304902926248587173536), 4861179281982221168443048683072;
    (-8879320504109353334731856243712), 5474241139457304159789072422592, 4861179281982221168443048683072, (-9481037388819400414621217617920)]

theorem f408desc0_compression_check :
    f408desc0ᵀ*f408rawM4Form*f408desc0=f408desc0Form := by
  have hD : natFourIntegerMatrix 210 f408desc0IntegerCoordinates=f408desc0 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 210 f408desc0IntegerCoordinates) (f408desc0) (by decide +kernel) a b
  have hV : f408desc0IntegerCoordinatesᵀ*f408rawInteger=f408desc0IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 15) => (f408desc0IntegerCoordinatesᵀ*f408rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 15) => (f408desc0IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 15) => (f408desc0IntegerCoordinatesᵀ*f408rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 15) => (f408desc0IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 15) => (f408desc0IntegerCoordinatesᵀ*f408rawInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 15) => (f408desc0IntegerLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 15) => (f408desc0IntegerCoordinatesᵀ*f408rawInteger) 3 j)
        (fun (_ : Fin 1) (j : Fin 15) => (f408desc0IntegerLeftProduct) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f408desc0IntegerLeftProduct*f408desc0IntegerCoordinates=f408desc0IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc0IntegerLeftProduct*f408desc0IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc0IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc0IntegerLeftProduct*f408desc0IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc0IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc0IntegerLeftProduct*f408desc0IntegerCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc0IntegerForm) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc0IntegerLeftProduct*f408desc0IntegerCoordinates) 3 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc0IntegerForm) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (210*1000000000000000000000000*210) f408desc0IntegerForm=f408desc0Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (210*1000000000000000000000000*210) f408desc0IntegerForm) (f408desc0Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 210
    f408rawInteger f408desc0IntegerCoordinates f408desc0IntegerLeftProduct f408desc0IntegerForm
    f408rawM4Form f408desc0 f408desc0Form f408_raw_integer_check hD hV hY hF

theorem f408desc0_source_form (x y : Fin 4 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0] (natFourWordBlock f408basis (complexify b408relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
          (natFourWordBlock f408basis (complexify b408relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f408desc0Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 0
    f408basis b408relative
    f408basis f408desc0 f408rawM4Form f408desc0Form
    f408desc0_actual f408_actual_raw_M4_matrix f408desc0_compression_check x y


#print axioms f408desc0_compression_check
#print axioms f408desc0_source_form
end TorusLean.BosonFiniteCertificate
