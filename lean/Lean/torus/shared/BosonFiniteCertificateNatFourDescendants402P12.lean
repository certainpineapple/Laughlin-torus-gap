import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates402
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger414
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

def f402desc12Form : Matrix (Fin 1) (Fin 1) ℚ :=
  !![(3603375383341953061608804027787347/19531250000000000000)]

private def f402desc12IntegerCoordinates : Matrix (Fin 47) (Fin 1) ℤ :=
  !![(-1);
    (-34);
    (-177);
    (-564);
    (-1243);
    (-2046);
    (-2673);
    (-1452);
    (-346);
    (-3192);
    (-8888);
    (-16940);
    (-24156);
    (-27984);
    (-6402);
    (-30360);
    (-48510);
    (-58608);
    (-30492);
    (-29700);
    (-76560);
    (-77616);
    (-39270);
    (-36036);
    (-1032);
    (-12276);
    (-28600);
    (-44550);
    (-52272);
    (-26796);
    (-40260);
    (-146520);
    (-166320);
    (-144144);
    (-89760);
    (-92400);
    (-11088);
    41580;
    (-32670);
    (-102960);
    (-13860);
    24948;
    55440;
    609840;
    173250;
    184800;
    438900]

private def f402desc12IntegerLeftProduct : Matrix (Fin 1) (Fin 47) ℤ :=
  !![0, 0, 0, 0, 0, 0, (-4905622213898708771558940412108800), (-8322470680049016232637507531673600), 0, 0, 0, 0, (-14269160167814703524604224716800), (-2392714366415091574501158052531200), 0, 0, 12508022342441116721376044236800, (-114871689227512651142388734208000), (-932898933620084951936076687206400), 620179211922518477705875660800, (-25569707468885101162072564070400), (-158115473622659142882526037760000), 125464176046979681060705207731200, 0, 0, 0, 0, 1841419283769190646205331046400, (-65883223444079590559661584102400), (-1062920219121191061082995971788800), 0, (-996512910391137467418170572800), (-42354251608079180710279785600000), (-126998784005992436041854230707200), 57391215103834176350188351872000, 7029166297307709146696326886400, 0, 0, 8053398025967132662628496384000, (-8381794818792963780746019763200), 103156498664527470560827776230400, 0, (-46395200701811208193852911667200), 0, 0, 0, 0]

private def f402desc12IntegerForm : Matrix (Fin 1) (Fin 1) ℤ :=
  !![184492819627107996754370766222712166400]

private theorem f402desc12_coordinates_decode : natFourIntegerMatrix 1 f402desc12IntegerCoordinates=f402desc12 := by
  ext a b
  exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 1 f402desc12IntegerCoordinates) (f402desc12) (by decide +kernel) a b

#print axioms f402desc12_coordinates_decode

private theorem f402desc12_left_row0_columns0 :
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 0=f402desc12IntegerLeftProduct 0 0) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 1=f402desc12IntegerLeftProduct 0 1) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 2=f402desc12IntegerLeftProduct 0 2) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 3=f402desc12IntegerLeftProduct 0 3) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 4=f402desc12IntegerLeftProduct 0 4) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 5=f402desc12IntegerLeftProduct 0 5) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 6=f402desc12IntegerLeftProduct 0 6) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 7=f402desc12IntegerLeftProduct 0 7) := by
  decide +kernel

#print axioms f402desc12_left_row0_columns0

private theorem f402desc12_left_row0_columns1 :
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 8=f402desc12IntegerLeftProduct 0 8) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 9=f402desc12IntegerLeftProduct 0 9) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 10=f402desc12IntegerLeftProduct 0 10) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 11=f402desc12IntegerLeftProduct 0 11) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 12=f402desc12IntegerLeftProduct 0 12) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 13=f402desc12IntegerLeftProduct 0 13) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 14=f402desc12IntegerLeftProduct 0 14) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 15=f402desc12IntegerLeftProduct 0 15) := by
  decide +kernel

#print axioms f402desc12_left_row0_columns1

private theorem f402desc12_left_row0_columns2 :
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 16=f402desc12IntegerLeftProduct 0 16) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 17=f402desc12IntegerLeftProduct 0 17) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 18=f402desc12IntegerLeftProduct 0 18) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 19=f402desc12IntegerLeftProduct 0 19) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 20=f402desc12IntegerLeftProduct 0 20) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 21=f402desc12IntegerLeftProduct 0 21) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 22=f402desc12IntegerLeftProduct 0 22) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 23=f402desc12IntegerLeftProduct 0 23) := by
  decide +kernel

#print axioms f402desc12_left_row0_columns2

private theorem f402desc12_left_row0_columns3 :
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 24=f402desc12IntegerLeftProduct 0 24) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 25=f402desc12IntegerLeftProduct 0 25) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 26=f402desc12IntegerLeftProduct 0 26) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 27=f402desc12IntegerLeftProduct 0 27) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 28=f402desc12IntegerLeftProduct 0 28) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 29=f402desc12IntegerLeftProduct 0 29) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 30=f402desc12IntegerLeftProduct 0 30) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 31=f402desc12IntegerLeftProduct 0 31) := by
  decide +kernel

#print axioms f402desc12_left_row0_columns3

private theorem f402desc12_left_row0_columns4 :
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 32=f402desc12IntegerLeftProduct 0 32) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 33=f402desc12IntegerLeftProduct 0 33) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 34=f402desc12IntegerLeftProduct 0 34) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 35=f402desc12IntegerLeftProduct 0 35) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 36=f402desc12IntegerLeftProduct 0 36) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 37=f402desc12IntegerLeftProduct 0 37) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 38=f402desc12IntegerLeftProduct 0 38) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 39=f402desc12IntegerLeftProduct 0 39) := by
  decide +kernel

#print axioms f402desc12_left_row0_columns4

private theorem f402desc12_left_row0_columns5 :
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 40=f402desc12IntegerLeftProduct 0 40) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 41=f402desc12IntegerLeftProduct 0 41) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 42=f402desc12IntegerLeftProduct 0 42) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 43=f402desc12IntegerLeftProduct 0 43) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 44=f402desc12IntegerLeftProduct 0 44) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 45=f402desc12IntegerLeftProduct 0 45) ∧
    ((f402desc12IntegerCoordinatesᵀ*f414rawInteger) 0 46=f402desc12IntegerLeftProduct 0 46) := by
  decide +kernel

#print axioms f402desc12_left_row0_columns5

theorem f402desc12_compression_check :
    f402desc12ᵀ*f414rawM4Form*f402desc12=f402desc12Form := by
  have hD := f402desc12_coordinates_decode
  have hV : f402desc12IntegerCoordinatesᵀ*f414rawInteger=f402desc12IntegerLeftProduct := by
    ext a b
    fin_cases a
    · fin_cases b
      · exact f402desc12_left_row0_columns0.1
      · exact f402desc12_left_row0_columns0.2.1
      · exact f402desc12_left_row0_columns0.2.2.1
      · exact f402desc12_left_row0_columns0.2.2.2.1
      · exact f402desc12_left_row0_columns0.2.2.2.2.1
      · exact f402desc12_left_row0_columns0.2.2.2.2.2.1
      · exact f402desc12_left_row0_columns0.2.2.2.2.2.2.1
      · exact f402desc12_left_row0_columns0.2.2.2.2.2.2.2
      · exact f402desc12_left_row0_columns1.1
      · exact f402desc12_left_row0_columns1.2.1
      · exact f402desc12_left_row0_columns1.2.2.1
      · exact f402desc12_left_row0_columns1.2.2.2.1
      · exact f402desc12_left_row0_columns1.2.2.2.2.1
      · exact f402desc12_left_row0_columns1.2.2.2.2.2.1
      · exact f402desc12_left_row0_columns1.2.2.2.2.2.2.1
      · exact f402desc12_left_row0_columns1.2.2.2.2.2.2.2
      · exact f402desc12_left_row0_columns2.1
      · exact f402desc12_left_row0_columns2.2.1
      · exact f402desc12_left_row0_columns2.2.2.1
      · exact f402desc12_left_row0_columns2.2.2.2.1
      · exact f402desc12_left_row0_columns2.2.2.2.2.1
      · exact f402desc12_left_row0_columns2.2.2.2.2.2.1
      · exact f402desc12_left_row0_columns2.2.2.2.2.2.2.1
      · exact f402desc12_left_row0_columns2.2.2.2.2.2.2.2
      · exact f402desc12_left_row0_columns3.1
      · exact f402desc12_left_row0_columns3.2.1
      · exact f402desc12_left_row0_columns3.2.2.1
      · exact f402desc12_left_row0_columns3.2.2.2.1
      · exact f402desc12_left_row0_columns3.2.2.2.2.1
      · exact f402desc12_left_row0_columns3.2.2.2.2.2.1
      · exact f402desc12_left_row0_columns3.2.2.2.2.2.2.1
      · exact f402desc12_left_row0_columns3.2.2.2.2.2.2.2
      · exact f402desc12_left_row0_columns4.1
      · exact f402desc12_left_row0_columns4.2.1
      · exact f402desc12_left_row0_columns4.2.2.1
      · exact f402desc12_left_row0_columns4.2.2.2.1
      · exact f402desc12_left_row0_columns4.2.2.2.2.1
      · exact f402desc12_left_row0_columns4.2.2.2.2.2.1
      · exact f402desc12_left_row0_columns4.2.2.2.2.2.2.1
      · exact f402desc12_left_row0_columns4.2.2.2.2.2.2.2
      · exact f402desc12_left_row0_columns5.1
      · exact f402desc12_left_row0_columns5.2.1
      · exact f402desc12_left_row0_columns5.2.2.1
      · exact f402desc12_left_row0_columns5.2.2.2.1
      · exact f402desc12_left_row0_columns5.2.2.2.2.1
      · exact f402desc12_left_row0_columns5.2.2.2.2.2.1
      · exact f402desc12_left_row0_columns5.2.2.2.2.2.2
  have hY : f402desc12IntegerLeftProduct*f402desc12IntegerCoordinates=f402desc12IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc12IntegerLeftProduct*f402desc12IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 1) => (f402desc12IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc12IntegerForm=f402desc12Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (1*1000000000000000000000000*1) f402desc12IntegerForm) (f402desc12Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 1
    f414rawInteger f402desc12IntegerCoordinates f402desc12IntegerLeftProduct f402desc12IntegerForm
    f414rawM4Form f402desc12 f402desc12Form f414_raw_integer_check hD hV hY hF

theorem f402desc12_source_form (x y : Fin 1 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[12] (natFourWordBlock f402basis (complexify b402relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[12]
          (natFourWordBlock f402basis (complexify b402relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f402desc12Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 12
    f402basis b402relative
    f414basis f402desc12 f414rawM4Form f402desc12Form
    f402desc12_actual f414_actual_raw_M4_matrix f402desc12_compression_check x y


#print axioms f402desc12_compression_check
#print axioms f402desc12_source_form
end TorusLean.BosonFiniteCertificate
