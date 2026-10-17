import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates408
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger409
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

def f408desc1Form : Matrix (Fin 4) (Fin 4) ℚ :=
  !![(7838105762179206681585447/170898437500000000000000), (405132538963482718988103513/2734375000000000000000000), (-3006119138077952004909984711/10937500000000000000000000), (61300329519608989164593053/2734375000000000000000000);
    (405132538963482718988103513/2734375000000000000000000), (-5959791810415585019749883373/43750000000000000000000000), (-3012316191005489566019340993/21875000000000000000000000), (1201780122600971501445531789/5468750000000000000000000);
    (-3006119138077952004909984711/10937500000000000000000000), (-3012316191005489566019340993/21875000000000000000000000), (-3046671712670714960367155523/43750000000000000000000000), (2110697251844927125973783397/10937500000000000000000000);
    (61300329519608989164593053/2734375000000000000000000), (1201780122600971501445531789/5468750000000000000000000), (2110697251844927125973783397/10937500000000000000000000), (-71509764731407274571628751/195312500000000000000000)]

private def f408desc1IntegerCoordinates : Matrix (Fin 18) (Fin 4) ℤ :=
  !![6, (-6), (-6), 10;
    (-30), 30, 30, (-50);
    120, (-15), 6, (-24);
    (-168), (-42), (-21), 56;
    84, 21, 21, 0;
    (-96), (-9), (-30), 64;
    336, (-21), (-147), 224;
    (-672), 252, 126, (-336);
    420, (-105), (-105), 0;
    0, 0, 189, (-196);
    0, (-315), (-105), 280;
    0, 210, 0, 0;
    0, (-105), 0, 0;
    0, 315, 252, (-448);
    0, (-105), 0, 560;
    0, (-315), (-630), 700;
    0, 210, 420, (-1120);
    0, 0, 0, 280]

private def f408desc1IntegerLeftProduct : Matrix (Fin 4) (Fin 18) ℤ :=
  !![0, (-18774041842525451198472887040), (-44646556281121682948828347776), (-22031901541753522484484690432), 11714501053883719625851270656, 11404304621987579690720572800, 61986062579030373473097543936, 48807705682571661583650066240, 36185404529718078250645920384, (-18815005952497348090088627520), (-420441240730452048039476736), (-16574408530957828881824772096), 44072327293078745552290513920, 24324776584925134426764171264, (-21239199722941246305359839872), 1539743675276075117446215936, (-15577106471701511938078421376), 9621816672860664888335674752;
    0, 13762829448870953584642467840, (-51976290594443271061957729344), (-12070249270096511162916234288), (-60696473538903455363714921376), (-11315381492071451398198392000), (-1470732890785802664515757216), (-28555425735895916146422144000), (-8396755293721044017497549824), (-24038223200761127164800317280), (-8167139767983058949708032464), (-8231268905476727145070384944), (-15737601935417454768108489120), (-18309007054145926282612873824), (-3488713512686323755509981088), (-6921407344947407247526773696), 2254802251158256815811728576, (-129570146365759054521828192);
    0, 25226608692705498618583246560, (-63228372823320241775700901824), 29762346286408189486382953344, (-72752843264020051025964904704), (-14004905520845701988100671040), (-11125216780643261212202991456), (-25527415489916347573140697776), (-17680899180441156154690649472), (-22936505182234781014596903840), (-6263394117422613301718155152), (-9620086763907368032607127504), (-14709473354304133222080457440), (-17686901990317189026013039584), (-2086161493109606608753033200), (-8593940191201680660224425920), 1735742509439878182463276896, (-495915186017024883636628752);
    0, (-44902737471560484349397988480), 128008967318291519962940350080, 14693326382852394270638504832, 106029931708057186392978759552, 22374781635040813182194578560, 13877645872040507130356292480, 47643231044192832044568807744, 17485236587258919607881028992, 42778142347149737104644949440, 14347184825554700803235690112, 20143486579028915365397003520, 28337895578363903157249809280, 31823664458744123704031422080, 6160560798168575712628891008, 13669276270910566711630918656, (-645435332562712525297833600), 744560766349268964234531840]

private def f408desc1IntegerForm : Matrix (Fin 4) (Fin 4) ℤ :=
  !![2022607515718819925769761427456, 6533977588403049291840133457664, (-12120672364730302483797058354752), 988651714492253777246556758784;
    6533977588403049291840133457664, (-6007470144898909699907882439984), (-6072829441067066965094991441888), 9691154908654234187656768346496;
    (-12120672364730302483797058354752), (-6072829441067066965094991441888), (-3071045086372080680050092767184), 8510331319438746171926294656704;
    988651714492253777246556758784, 9691154908654234187656768346496, 8510331319438746171926294656704, (-16146332798233911340077198945792)]

theorem f408desc1_compression_check :
    f408desc1ᵀ*f409rawM4Form*f408desc1=f408desc1Form := by
  have hD : natFourIntegerMatrix 210 f408desc1IntegerCoordinates=f408desc1 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 210 f408desc1IntegerCoordinates) (f408desc1) (by decide +kernel) a b
  have hV : f408desc1IntegerCoordinatesᵀ*f409rawInteger=f408desc1IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 18) => (f408desc1IntegerCoordinatesᵀ*f409rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 18) => (f408desc1IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 18) => (f408desc1IntegerCoordinatesᵀ*f409rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 18) => (f408desc1IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 18) => (f408desc1IntegerCoordinatesᵀ*f409rawInteger) 2 j)
        (fun (_ : Fin 1) (j : Fin 18) => (f408desc1IntegerLeftProduct) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 18) => (f408desc1IntegerCoordinatesᵀ*f409rawInteger) 3 j)
        (fun (_ : Fin 1) (j : Fin 18) => (f408desc1IntegerLeftProduct) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f408desc1IntegerLeftProduct*f408desc1IntegerCoordinates=f408desc1IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc1IntegerLeftProduct*f408desc1IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc1IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc1IntegerLeftProduct*f408desc1IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc1IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc1IntegerLeftProduct*f408desc1IntegerCoordinates) 2 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc1IntegerForm) 2 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc1IntegerLeftProduct*f408desc1IntegerCoordinates) 3 j)
        (fun (_ : Fin 1) (j : Fin 4) => (f408desc1IntegerForm) 3 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (210*1000000000000000000000000*210) f408desc1IntegerForm=f408desc1Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (210*1000000000000000000000000*210) f408desc1IntegerForm) (f408desc1Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 210
    f409rawInteger f408desc1IntegerCoordinates f408desc1IntegerLeftProduct f408desc1IntegerForm
    f409rawM4Form f408desc1 f408desc1Form f409_raw_integer_check hD hV hY hF

theorem f408desc1_source_form (x y : Fin 4 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1] (natFourWordBlock f408basis (complexify b408relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
          (natFourWordBlock f408basis (complexify b408relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f408desc1Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 1
    f408basis b408relative
    f409basis f408desc1 f409rawM4Form f408desc1Form
    f408desc1_actual f409_actual_raw_M4_matrix f408desc1_compression_check x y


#print axioms f408desc1_compression_check
#print axioms f408desc1_source_form
end TorusLean.BosonFiniteCertificate
