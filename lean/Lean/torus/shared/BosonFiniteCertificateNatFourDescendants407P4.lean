import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates407
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger411
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

def f407desc4Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(29933510714711061515116572951/390625000000000000000000), (-10010168127412801631381442807/97656250000000000000000);
    (-10010168127412801631381442807/97656250000000000000000), (26354330784368884260877647017/195312500000000000000000)]

private def f407desc4IntegerCoordinates : Matrix (Fin 27) (Fin 2) ℤ :=
  !![3, (-4);
    15, (-20);
    (-3), 24;
    3, 56;
    12, 4;
    (-36), (-52);
    (-24), 12;
    (-126), 128;
    120, (-80);
    96, (-88);
    (-72), 56;
    (-54), (-108);
    (-12), (-344);
    (-324), 512;
    12, 24;
    150, 200;
    (-36), 28;
    144, (-112);
    456, (-288);
    108, 176;
    126, (-68);
    (-432), 256;
    (-270), 40;
    660, (-1720);
    (-486), 708;
    (-630), 1060;
    600, (-400)]

private def f407desc4IntegerLeftProduct : Matrix (Fin 2) (Fin 27) ℤ :=
  !![0, 0, 0, (-503738011852863621642221137920), (-354911056319654158422592416384), (-972591285871220514391342425600), 0, (-5352847940135647428554649600), 58528342177831392565654955520, (-308629864425488363975494810368), (-793526774376435149902791219840), 421253772519467115323786880, (-48283955020273818492736611840), (-355834429050158526334461107904), (-170254489230031830419724681600), (-76905243663838030815902658432), (-3112961636107781920563333120), (-16823707259296080280420362240), (-15557343019172380339541573760), (-257048850958464846879029544768), (-30591281365267259621783767680), (-120855461184198810645632824320), (-40191240381427119174972715008), (-18110619176101817730168897792), (-135190858835995978265721642240), (-40608117341368900571747108736), 12965027245571009405217323520;
    0, 0, 0, 639702159110662159305333711360, 311031896764078070639337756672, 776867473776306168587439014400, 0, (-162877421473778133468057600), (-59558448397327803587342568960), 207513223969611393104519937024, 855975121698165396780570462720, 30825150317551685687489372160, 77170569550959303839636421120, 433863066804857255573480984832, 281347142464430173447463001600, 135682000162287497565278973696, (-94721599676863579509411840), 11819501883555353416599851520, (-43079173258737930117802053120), 373288739696205019364864185344, 87757936849926926817821591040, 202097672094036514194095535360, 112891075325290201473039919104, 43645815677758969974079881216, 186260463928175737166085784320, 36070073618423843379286695168, (-16061026074014895660413602560)]

private def f407desc4IntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![275867234746777142923314336316416, (-369014837848945519339245507637248);
    (-369014837848945519339245507637248), 485763025017487274696496789817344]

theorem f407desc4_compression_check :
    f407desc4ᵀ*f411rawM4Form*f407desc4=f407desc4Form := by
  have hD : natFourIntegerMatrix 60 f407desc4IntegerCoordinates=f407desc4 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 60 f407desc4IntegerCoordinates) (f407desc4) (by decide +kernel) a b
  have hV : f407desc4IntegerCoordinatesᵀ*f411rawInteger=f407desc4IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f407desc4IntegerCoordinatesᵀ*f411rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f407desc4IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 27) => (f407desc4IntegerCoordinatesᵀ*f411rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 27) => (f407desc4IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f407desc4IntegerLeftProduct*f407desc4IntegerCoordinates=f407desc4IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc4IntegerLeftProduct*f407desc4IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc4IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc4IntegerLeftProduct*f407desc4IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f407desc4IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (60*1000000000000000000000000*60) f407desc4IntegerForm=f407desc4Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (60*1000000000000000000000000*60) f407desc4IntegerForm) (f407desc4Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 60
    f411rawInteger f407desc4IntegerCoordinates f407desc4IntegerLeftProduct f407desc4IntegerForm
    f411rawM4Form f407desc4 f407desc4Form f411_raw_integer_check hD hV hY hF

theorem f407desc4_source_form (x y : Fin 2 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4] (natFourWordBlock f407basis (complexify b407relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
          (natFourWordBlock f407basis (complexify b407relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f407desc4Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 4
    f407basis b407relative
    f411basis f407desc4 f411rawM4Form f407desc4Form
    f407desc4_actual f411_actual_raw_M4_matrix f407desc4_compression_check x y


#print axioms f407desc4_compression_check
#print axioms f407desc4_source_form
end TorusLean.BosonFiniteCertificate
