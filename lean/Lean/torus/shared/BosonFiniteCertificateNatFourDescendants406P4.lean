import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates406
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger410
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

def f406desc4Form : Matrix (Fin 3) (Fin 3) ℚ :=
  !![(17875591418865121881579522819/195312500000000000000000), (-12201047601586429995424603683/390625000000000000000000), (-9349997331383823736399355583/390625000000000000000000);
    (-12201047601586429995424603683/390625000000000000000000), (2821304862989968077052596141/48828125000000000000000), (4360408000281281588295464557/97656250000000000000000);
    (-9349997331383823736399355583/390625000000000000000000), (4360408000281281588295464557/97656250000000000000000), (5285119485271924534691498873/146484375000000000000000)]

private def f406desc4IntegerCoordinates : Matrix (Fin 23) (Fin 3) ℤ :=
  !![(-3), 3, 3;
    (-18), 18, 18;
    (-27), (-3), (-13);
    (-48), (-12), (-52);
    (-12), 42, (-28);
    18, 42, 2;
    36, (-6), 4;
    72, (-132), (-92);
    (-96), (-84), (-4);
    180, 0, 180;
    (-162), 12, 82;
    (-360), 180, 300;
    90, 30, 70;
    180, 60, (-160);
    144, (-24), (-24);
    216, 84, 4;
    0, (-120), (-40);
    180, (-270), (-120);
    (-540), 540, 240;
    0, (-540), (-780);
    240, (-240), (-320);
    (-270), 300, 270;
    180, 120, 460]

private def f406desc4IntegerLeftProduct : Matrix (Fin 3) (Fin 23) ℤ :=
  !![0, 0, (-80481676713328534409163659520), (-54284811395692832930861709696), 33108892212570593099111796096, 482409861039349906174355646720, 852703285689316140097536000, 46613086657363913748794640000, 19297420380479567054961149184, 109578106460388785923875676608, (-48127451635755584141771255040), 3150659829032879214010296384, (-3536693604611295202930411008), 29341012184666336660347929600, 7256180600240973076853291520, (-3673347673113625203898168320), (-685445603267360973968277120), (-9236404520733118273735726080), (-54434821483099752667108796160), 17311950719243202160699250688, 13641336735163959041053104384, (-16749995232921478159455341568), 3566807016018000995797334784;
    0, 0, (-11468620826135111164069255680), 90432084432190593812919417216, 132053343125401020228946694784, 224509780316911014643187162880, (-1778953361303169272383948800), (-19716026042798287838661686400), 19262319087238558789466261376, 50267704049885497891409980992, (-4780363574217874724759439360), 6009287806863482593579903296, 19895016352962031905512337408, (-19849231142114638940835171840), (-9097142777650283146029630720), (-8967980764332550775504897280), (-4377180335422753887551239680), (-12220574472324464684155061760), 26637850562605821361247016960, (-20520482601577003145901324288), (-18890391317275758323007051264), 13556208454520848689966156288, (-5865278079443761991502607104);
    0, 0, 27407100271492576942824760320, (-65522695706274229999469541504), (-105708183420582250945223826816), 235217996268499834065026215680, (-1456271805523148241346252800), 7832037364080742845703747200, 10442624571216932432118817536, 18523888618270341079727260992, 3644318323753565571862890240, 8739624107866906926608243136, (-215638129005705695728257792), (-341077394586266356011287040), (-1704084188326976672298270720), (-4515191655493932075999521280), (-3479477166662293907578592640), (-36053678745061268167449792000), 27485862564796067402771439360, (-11890148457593609830138053888), (-5915846790198838758846645504), 10125140720650025640425250048, (-9830379198221560944136207104)]

private def f406desc4IntegerForm : Matrix (Fin 3) (Fin 3) ℤ :=
  !![82370725258130481630318441149952, (-28111213674055134709458286885632), (-21542393851508329888664115263232);
    (-28111213674055134709458286885632), 52002291234631091596233452070912, 40185520130592291117731001357312;
    (-21542393851508329888664115263232), 40185520130592291117731001357312, 32471774117510704341144569075712]

theorem f406desc4_compression_check :
    f406desc4ᵀ*f410rawM4Form*f406desc4=f406desc4Form := by
  have hD : natFourIntegerMatrix 30 f406desc4IntegerCoordinates=f406desc4 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 30 f406desc4IntegerCoordinates) (f406desc4) (by decide +kernel) a b
  have hV : f406desc4IntegerCoordinatesᵀ*f410rawInteger=f406desc4IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f406desc4IntegerCoordinatesᵀ*f410rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f406desc4IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f406desc4IntegerCoordinatesᵀ*f410rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f406desc4IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f406desc4IntegerCoordinatesᵀ*f410rawInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f406desc4IntegerLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f406desc4IntegerLeftProduct*f406desc4IntegerCoordinates=f406desc4IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc4IntegerLeftProduct*f406desc4IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc4IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc4IntegerLeftProduct*f406desc4IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc4IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc4IntegerLeftProduct*f406desc4IntegerCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 3) => (f406desc4IntegerForm) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (30*1000000000000000000000000*30) f406desc4IntegerForm=f406desc4Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (30*1000000000000000000000000*30) f406desc4IntegerForm) (f406desc4Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 30
    f410rawInteger f406desc4IntegerCoordinates f406desc4IntegerLeftProduct f406desc4IntegerForm
    f410rawM4Form f406desc4 f406desc4Form f410_raw_integer_check hD hV hY hF

theorem f406desc4_source_form (x y : Fin 3 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4] (natFourWordBlock f406basis (complexify b406relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
          (natFourWordBlock f406basis (complexify b406relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f406desc4Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 4
    f406basis b406relative
    f410basis f406desc4 f410rawM4Form f406desc4Form
    f406desc4_actual f410_actual_raw_M4_matrix f406desc4_compression_check x y


#print axioms f406desc4_compression_check
#print axioms f406desc4_source_form
end TorusLean.BosonFiniteCertificate
