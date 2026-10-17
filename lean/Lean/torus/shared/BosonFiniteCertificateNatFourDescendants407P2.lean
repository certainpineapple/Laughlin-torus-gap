import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates407
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger409
import torus.shared.BosonFiniteCertificateNatFourRaise407
import torus.shared.BosonFiniteCertificateNatFourRaise408
import torus.shared.BosonFiniteCertificateNatFourRaise409
import torus.shared.BosonFiniteCertificateNatFourRaise410
import torus.shared.BosonFiniteCertificateNatFourRaise411
import torus.shared.BosonFiniteCertificateNatFourRaise412
import torus.shared.BosonFiniteCertificateNatFourRaise413
import torus.shared.BosonFiniteCertificateNatFourRaise414
import torus.shared.BosonFiniteCertificateNatFourRaise415
import torus.shared.BosonFiniteCertificate407

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

def f407desc2Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(1987317704922529684870818393/3125000000000000000000000), (-2892625425891689097937641899/3125000000000000000000000);
    (-2892625425891689097937641899/3125000000000000000000000), (527950041419328195509389981/585937500000000000000000)]

private def f407desc2IntegerCoordinates : Matrix (Fin 18) (Fin 2) ℤ :=
  !![3, (-4);
    (-3), 4;
    (-6), 28;
    18, (-4);
    (-18), (-16);
    (-30), 20;
    36, (-88);
    60, (-40);
    (-30), 80;
    (-54), (-28);
    (-60), 120;
    60, (-40);
    30, (-20);
    54, 28;
    30, (-20);
    (-270), 260;
    180, (-440);
    0, 160]

private def f407desc2IntegerLeftProduct : Matrix (Fin 2) (Fin 18) ℤ :=
  !![0, 2349171602118359725721209920, 10773539667281045343950229312, (-11754765819663611663191763808), (-16395122211949834293590436672), 598792747737896914106681280, (-3392828141010112518569235072), (-7663249328736404716357605120), (-8327284686754666428137370048), (-3310544178161940843008088480), (-370241933943307753235915136), 10018295406836321262572896704, (-5558808834520541087631102720), (-7635274284399041287545078528), 2124760884195489908035957344, (-5024922610580072521885109376), 5467499263293591259051352064, 1913491568453972002447951008;
    0, 18315244639581725764971373440, (-18384929189657463462872215296), 2094420022878941249992017984, 24272113877560726023457305216, 438343558775208560457212160, 5481693818404102706260747776, 2708044035480410372407533120, 13184641618984046640944465664, 9479190595692189621929819520, 1193783235221661863589977088, (-7721866590545700976120647552), 10473996853033606313676149760, 10024228015484504508679989504, 1466831763605890618751312448, 6771927053767236540848775168, (-5355008287919568097541235072), (-4602072473902764783417777984)]

private def f407desc2IntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![2289389996070754196971182788736, (-3332304490627225840824163467648);
    (-3332304490627225840824163467648), 3243725054480352433209692043264]

theorem f407desc2_compression_check :
    f407desc2ᵀ*f409rawM4Form*f407desc2=f407desc2Form := by
  have hD : natFourIntegerMatrix 60 f407desc2IntegerCoordinates=f407desc2 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 60 f407desc2IntegerCoordinates) (f407desc2) (by decide +kernel) a b
  have hV : f407desc2IntegerCoordinatesᵀ*f409rawInteger=f407desc2IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 18) => (f407desc2IntegerCoordinatesᵀ*f409rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 18) => (f407desc2IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 18) => (f407desc2IntegerCoordinatesᵀ*f409rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 18) => (f407desc2IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f407desc2IntegerLeftProduct*f407desc2IntegerCoordinates=f407desc2IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc2IntegerLeftProduct*f407desc2IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc2IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc2IntegerLeftProduct*f407desc2IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc2IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (60*1000000000000000000000000*60) f407desc2IntegerForm=f407desc2Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (60*1000000000000000000000000*60) f407desc2IntegerForm) (f407desc2Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 60
    f409rawInteger f407desc2IntegerCoordinates f407desc2IntegerLeftProduct f407desc2IntegerForm
    f409rawM4Form f407desc2 f407desc2Form f409_raw_integer_check hD hV hY hF

theorem f407desc2_source_form (x y : Fin 2 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2] (natFourWordBlock f407basis (complexify b407relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
          (natFourWordBlock f407basis (complexify b407relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f407desc2Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 2
    f407basis b407relative
    f409basis f407desc2 f409rawM4Form f407desc2Form
    f407desc2_actual f409_actual_raw_M4_matrix f407desc2_compression_check x y


#print axioms f407desc2_compression_check
#print axioms f407desc2_source_form
end TorusLean.BosonFiniteCertificate
