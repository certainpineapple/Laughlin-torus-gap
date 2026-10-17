import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates406
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger407
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
import torus.shared.BosonFiniteCertificate406

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

def f406desc1Form : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(-1119834963789163937684603931/6250000000000000000000000), (364002787905977068863437901/6250000000000000000000000), (153100904970347382481284301/6250000000000000000000000);
    (364002787905977068863437901/6250000000000000000000000), (-411951149150840284534367671/6250000000000000000000000), (-2104905972518180297895475513/18750000000000000000000000);
    (153100904970347382481284301/6250000000000000000000000), (-2104905972518180297895475513/18750000000000000000000000), (-7332750092245944467861483239/56250000000000000000000000)]

private def f406desc1IntegerCoordinates : Matrix (Fin 11) (Fin 3) ℤ :=
  !![(-3), 3, 3;
    9, (-9), (-9);
    (-27), (-3), (-13);
    15, 15, 5;
    36, (-6), 4;
    (-90), 30, 70;
    60, (-60), (-20);
    0, 30, (-20);
    0, 30, 0;
    0, (-60), (-80);
    0, 30, 60]

private def f406desc1IntegerLeftProduct : Matrix (Fin 3) (Fin 11) ℤ :=
  !![5821472680229850943318643520, (-991181148756811097763593160), 1997884012150121366822956992, 584134573113461241107208648, (-1074260388621417676267782240), 184270224481174669088559600, (-573877374685177324425541056), 342607716605943130513526712, (-1105016467376770294588797960), 150703972967869047190282320, 292372529087695428274888728;
    (-5997227864149598700696969600), (-413815738670546160353962680), 1195776033457608753371326848, 152880586781534638538043672, 62667337319116117460867520, (-816730875984443774026923120), (-126999989440148097843822144), (-273085520701797574063545912), (-314573590386750768218345160), (-133126938467459203696165440), (-561980542433643051012333288);
    (-6411434891535418113095613120), (-431978707141630711220928120), 2632089926128136808357266368, (-149172265052589053483762088), 105760491726203113653622560, (-515359986789219574271049520), 496904491224565016516403456, (-101210541364773800314303352), (-506421616066506575149034520), (-15383974082375094154597680), (-411319277028807253923146808)]

private def f406desc1IntegerForm : Matrix (Fin 3) (Fin 3) ℤ :=
  !![(-161256234785639607026582966064), 52416401458460697916335057744, 22046530315730023077304939344;
    52416401458460697916335057744, (-59320965477721000972948944624), (-101035486680872654298982824624);
    22046530315730023077304939344, (-101035486680872654298982824624), (-117324001475935111485783731824)]

theorem f406desc1_compression_check :
    f406desc1ᵀ*f407rawM4Form*f406desc1=f406desc1Form := by
  have hD : natFourIntegerMatrix 30 f406desc1IntegerCoordinates=f406desc1 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 30 f406desc1IntegerCoordinates) (f406desc1) (by decide +kernel) a b
  have hV : f406desc1IntegerCoordinatesᵀ*f407rawInteger=f406desc1IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 11) => (f406desc1IntegerCoordinatesᵀ*f407rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 11) => (f406desc1IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 11) => (f406desc1IntegerCoordinatesᵀ*f407rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 11) => (f406desc1IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 11) => (f406desc1IntegerCoordinatesᵀ*f407rawInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 11) => (f406desc1IntegerLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f406desc1IntegerLeftProduct*f406desc1IntegerCoordinates=f406desc1IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc1IntegerLeftProduct*f406desc1IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc1IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc1IntegerLeftProduct*f406desc1IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc1IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc1IntegerLeftProduct*f406desc1IntegerCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc1IntegerForm) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (30*1000000000000000000000000*30) f406desc1IntegerForm=f406desc1Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (30*1000000000000000000000000*30) f406desc1IntegerForm) (f406desc1Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 30
    f407rawInteger f406desc1IntegerCoordinates f406desc1IntegerLeftProduct f406desc1IntegerForm
    f407rawM4Form f406desc1 f406desc1Form f407_raw_integer_check hD hV hY hF

theorem f406desc1_source_form (x y : Fin 3 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1] (natFourWordBlock f406basis (complexify b406relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
          (natFourWordBlock f406basis (complexify b406relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f406desc1Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 1
    f406basis b406relative
    f407basis f406desc1 f407rawM4Form f406desc1Form
    f406desc1_actual f407_actual_raw_M4_matrix f406desc1_compression_check x y


#print axioms f406desc1_compression_check
#print axioms f406desc1_source_form
end TorusLean.BosonFiniteCertificate
