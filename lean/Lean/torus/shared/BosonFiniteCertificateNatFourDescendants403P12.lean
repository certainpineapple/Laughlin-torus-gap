import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates403
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger415
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

def f403desc12Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(1644213696182584558230042768458457/156250000000000000000)]

private def f403desc12IntegerCoordinates : Matrix (Fin 54) (Fin 1) ℤ :=
  !![1;
    33;
    159;
    429;
    663;
    429;
    (-429);
    (-1287);
    330;
    2838;
    6600;
    7986;
    1452;
    (-10890);
    (-8712);
    5274;
    19668;
    13530;
    (-18414);
    (-53064);
    11220;
    (-18810);
    (-96624);
    (-69300);
    (-58410);
    (-218988);
    (-47124);
    998;
    11484;
    23100;
    22110;
    (-2970);
    (-32472);
    38214;
    125400;
    74250;
    (-80784);
    (-85932);
    69300;
    (-39600);
    (-277200);
    (-159390);
    (-241164);
    37290;
    157410;
    77220;
    (-58212);
    182160;
    138600;
    (-16632);
    20790;
    92400;
    304920;
    150150]

private def f403desc12IntegerLeftProduct : Matrix (Fin 1) (Fin 54) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, (-6097614701828537081323694084889600), 0, 0, 0, 0, 0, (-64852858819507677609096522547200), (-1965707529344298979437764788992000), 0, 0, 0, 8909411479875301414029799219200, (-303540506304936016746803599641600), 0, (-1150208180360613619902642585600), 70151708969924966049691020441600, 0, (-61527887577120953282826470400000), 0, 0, 0, 0, 0, 0, 11020586231863826780723269632000, (-266996010859777784097723698611200), 0, 0, (-4016713040851061994989027328000), 64774075191949687244840124134400, 0, 4700720734515913532049154252800, (-2660925721496202507250331366400), 0, 0, 0, 0, (-276958877963060209730700902400), (-44583054944629713961181128704000), 0, 19661540688970315619245906636800, 0, 0, 0, 0, 0, 0]

private def f403desc12IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![42091870622274164690689094872536499200]

private theorem f403desc12_coordinates_decode : natFourIntegerMatrix 2 f403desc12IntegerCoordinates=f403desc12 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 2 f403desc12IntegerCoordinates) (f403desc12) (by decide +kernel) a b

#print axioms f403desc12_coordinates_decode

private theorem f403desc12_left_row0_columns0 :
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 0=f403desc12IntegerLeftProduct 0 0) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 1=f403desc12IntegerLeftProduct 0 1) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 2=f403desc12IntegerLeftProduct 0 2) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 3=f403desc12IntegerLeftProduct 0 3) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 4=f403desc12IntegerLeftProduct 0 4) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 5=f403desc12IntegerLeftProduct 0 5) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 6=f403desc12IntegerLeftProduct 0 6) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 7=f403desc12IntegerLeftProduct 0 7) := by
  decide +kernel

#print axioms f403desc12_left_row0_columns0

private theorem f403desc12_left_row0_columns1 :
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 8=f403desc12IntegerLeftProduct 0 8) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 9=f403desc12IntegerLeftProduct 0 9) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 10=f403desc12IntegerLeftProduct 0 10) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 11=f403desc12IntegerLeftProduct 0 11) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 12=f403desc12IntegerLeftProduct 0 12) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 13=f403desc12IntegerLeftProduct 0 13) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 14=f403desc12IntegerLeftProduct 0 14) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 15=f403desc12IntegerLeftProduct 0 15) := by
  decide +kernel

#print axioms f403desc12_left_row0_columns1

private theorem f403desc12_left_row0_columns2 :
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 16=f403desc12IntegerLeftProduct 0 16) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 17=f403desc12IntegerLeftProduct 0 17) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 18=f403desc12IntegerLeftProduct 0 18) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 19=f403desc12IntegerLeftProduct 0 19) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 20=f403desc12IntegerLeftProduct 0 20) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 21=f403desc12IntegerLeftProduct 0 21) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 22=f403desc12IntegerLeftProduct 0 22) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 23=f403desc12IntegerLeftProduct 0 23) := by
  decide +kernel

#print axioms f403desc12_left_row0_columns2

private theorem f403desc12_left_row0_columns3 :
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 24=f403desc12IntegerLeftProduct 0 24) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 25=f403desc12IntegerLeftProduct 0 25) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 26=f403desc12IntegerLeftProduct 0 26) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 27=f403desc12IntegerLeftProduct 0 27) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 28=f403desc12IntegerLeftProduct 0 28) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 29=f403desc12IntegerLeftProduct 0 29) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 30=f403desc12IntegerLeftProduct 0 30) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 31=f403desc12IntegerLeftProduct 0 31) := by
  decide +kernel

#print axioms f403desc12_left_row0_columns3

private theorem f403desc12_left_row0_columns4 :
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 32=f403desc12IntegerLeftProduct 0 32) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 33=f403desc12IntegerLeftProduct 0 33) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 34=f403desc12IntegerLeftProduct 0 34) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 35=f403desc12IntegerLeftProduct 0 35) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 36=f403desc12IntegerLeftProduct 0 36) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 37=f403desc12IntegerLeftProduct 0 37) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 38=f403desc12IntegerLeftProduct 0 38) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 39=f403desc12IntegerLeftProduct 0 39) := by
  decide +kernel

#print axioms f403desc12_left_row0_columns4

private theorem f403desc12_left_row0_columns5 :
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 40=f403desc12IntegerLeftProduct 0 40) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 41=f403desc12IntegerLeftProduct 0 41) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 42=f403desc12IntegerLeftProduct 0 42) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 43=f403desc12IntegerLeftProduct 0 43) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 44=f403desc12IntegerLeftProduct 0 44) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 45=f403desc12IntegerLeftProduct 0 45) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 46=f403desc12IntegerLeftProduct 0 46) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 47=f403desc12IntegerLeftProduct 0 47) := by
  decide +kernel

#print axioms f403desc12_left_row0_columns5

private theorem f403desc12_left_row0_columns6 :
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 48=f403desc12IntegerLeftProduct 0 48) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 49=f403desc12IntegerLeftProduct 0 49) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 50=f403desc12IntegerLeftProduct 0 50) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 51=f403desc12IntegerLeftProduct 0 51) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 52=f403desc12IntegerLeftProduct 0 52) ∧
    ((f403desc12IntegerCoordinatesᵀ*f415rawInteger) 0 53=f403desc12IntegerLeftProduct 0 53) := by
  decide +kernel

#print axioms f403desc12_left_row0_columns6

theorem f403desc12_compression_check :
    f403desc12ᵀ*f415rawM4Form*f403desc12=f403desc12Form := by
  have hD := f403desc12_coordinates_decode
  have hV : f403desc12IntegerCoordinatesᵀ*f415rawInteger=f403desc12IntegerLeftProduct := by
    ext a b
    fin_cases a
    · fin_cases b
      · exact f403desc12_left_row0_columns0.1
      · exact f403desc12_left_row0_columns0.2.1
      · exact f403desc12_left_row0_columns0.2.2.1
      · exact f403desc12_left_row0_columns0.2.2.2.1
      · exact f403desc12_left_row0_columns0.2.2.2.2.1
      · exact f403desc12_left_row0_columns0.2.2.2.2.2.1
      · exact f403desc12_left_row0_columns0.2.2.2.2.2.2.1
      · exact f403desc12_left_row0_columns0.2.2.2.2.2.2.2
      · exact f403desc12_left_row0_columns1.1
      · exact f403desc12_left_row0_columns1.2.1
      · exact f403desc12_left_row0_columns1.2.2.1
      · exact f403desc12_left_row0_columns1.2.2.2.1
      · exact f403desc12_left_row0_columns1.2.2.2.2.1
      · exact f403desc12_left_row0_columns1.2.2.2.2.2.1
      · exact f403desc12_left_row0_columns1.2.2.2.2.2.2.1
      · exact f403desc12_left_row0_columns1.2.2.2.2.2.2.2
      · exact f403desc12_left_row0_columns2.1
      · exact f403desc12_left_row0_columns2.2.1
      · exact f403desc12_left_row0_columns2.2.2.1
      · exact f403desc12_left_row0_columns2.2.2.2.1
      · exact f403desc12_left_row0_columns2.2.2.2.2.1
      · exact f403desc12_left_row0_columns2.2.2.2.2.2.1
      · exact f403desc12_left_row0_columns2.2.2.2.2.2.2.1
      · exact f403desc12_left_row0_columns2.2.2.2.2.2.2.2
      · exact f403desc12_left_row0_columns3.1
      · exact f403desc12_left_row0_columns3.2.1
      · exact f403desc12_left_row0_columns3.2.2.1
      · exact f403desc12_left_row0_columns3.2.2.2.1
      · exact f403desc12_left_row0_columns3.2.2.2.2.1
      · exact f403desc12_left_row0_columns3.2.2.2.2.2.1
      · exact f403desc12_left_row0_columns3.2.2.2.2.2.2.1
      · exact f403desc12_left_row0_columns3.2.2.2.2.2.2.2
      · exact f403desc12_left_row0_columns4.1
      · exact f403desc12_left_row0_columns4.2.1
      · exact f403desc12_left_row0_columns4.2.2.1
      · exact f403desc12_left_row0_columns4.2.2.2.1
      · exact f403desc12_left_row0_columns4.2.2.2.2.1
      · exact f403desc12_left_row0_columns4.2.2.2.2.2.1
      · exact f403desc12_left_row0_columns4.2.2.2.2.2.2.1
      · exact f403desc12_left_row0_columns4.2.2.2.2.2.2.2
      · exact f403desc12_left_row0_columns5.1
      · exact f403desc12_left_row0_columns5.2.1
      · exact f403desc12_left_row0_columns5.2.2.1
      · exact f403desc12_left_row0_columns5.2.2.2.1
      · exact f403desc12_left_row0_columns5.2.2.2.2.1
      · exact f403desc12_left_row0_columns5.2.2.2.2.2.1
      · exact f403desc12_left_row0_columns5.2.2.2.2.2.2.1
      · exact f403desc12_left_row0_columns5.2.2.2.2.2.2.2
      · exact f403desc12_left_row0_columns6.1
      · exact f403desc12_left_row0_columns6.2.1
      · exact f403desc12_left_row0_columns6.2.2.1
      · exact f403desc12_left_row0_columns6.2.2.2.1
      · exact f403desc12_left_row0_columns6.2.2.2.2.1
      · exact f403desc12_left_row0_columns6.2.2.2.2.2
  have hY : f403desc12IntegerLeftProduct*f403desc12IntegerCoordinates=f403desc12IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc12IntegerLeftProduct*f403desc12IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f403desc12IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc12IntegerForm=f403desc12Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (2*1000000000000000000000000*2) f403desc12IntegerForm) (f403desc12Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 2
    f415rawInteger f403desc12IntegerCoordinates f403desc12IntegerLeftProduct f403desc12IntegerForm
    f415rawM4Form f403desc12 f403desc12Form f415_raw_integer_check hD hV hY hF

theorem f403desc12_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[12] (natFourWordBlock f403basis (complexify b403relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[12]
          (natFourWordBlock f403basis (complexify b403relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f403desc12Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 12
    f403basis b403relative
    f415basis f403desc12 f415rawM4Form f403desc12Form
    f403desc12_actual f415_actual_raw_M4_matrix f403desc12_compression_check x y


#print axioms f403desc12_compression_check
#print axioms f403desc12_source_form
end TorusLean.BosonFiniteCertificate
