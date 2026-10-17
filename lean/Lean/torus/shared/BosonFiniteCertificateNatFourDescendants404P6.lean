import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendantCoordinates404
import torus.shared.BosonFiniteCertificateNatFourDescendantCore
import torus.shared.BosonFiniteCertificateNatFourRawInteger410
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
import torus.shared.BosonFiniteCertificate404

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

def f404desc6Form : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(11356045701081262616695845261/1953125000000000000000), (2619513799227793303268781633/781250000000000000000);
    (2619513799227793303268781633/781250000000000000000), (7819583954590942529308535637/976562500000000000000)]

private def f404desc6IntegerCoordinates : Matrix (Fin 23) (Fin 2) ℤ :=
  !![1, (-1);
    14, (-14);
    27, (-21);
    32, 4;
    34, 56;
    18, 42;
    42, (-48);
    72, (-84);
    24, 84;
    48, 252;
    (-24), (-42);
    24, (-252);
    90, (-210);
    200, (-560);
    0, (-24);
    (-240), 108;
    (-288), 312;
    (-90), 180;
    (-504), 288;
    (-120), 60;
    160, (-160);
    0, 90;
    480, (-60)]

private def f404desc6IntegerLeftProduct : Matrix (Fin 2) (Fin 23) ℤ :=
  !![0, 0, (-151100392703541011312841457920), 45038446470719969381418494592, 252466607787046179674649936768, 377764275342142191728065178880, 1285414329610833336883906560, (-3628163143497248416736208000), (-340230953028898617467057280), 59178848359165276522276301760, (-22213541010510522039822428160), (-18868443713887550584788585792), (-5410916750742911120784349440), (-1389531727787807975009614848), 4008733963962283662625209600, (-14335565770703869127336574720), (-22644136181508417469167609600), (-8916085478574251374080706560), (-49544161501888112758093463040), (-3482221376987079676993642752), (-4832059862266156431374238720), (-17874721066671817555644935424), 4715533098293265658006804224;
    0, 0, 40379775193745105613600453120, 128756691471685646666413231488, 345108505694283143737277166720, 713476165783682418765930351360, (-1163187242344641528096768000), (-32333401569799044840315588480), 51746836164647741642236285440, 138469089242579269615789004352, (-32488933688897186609564670720), 21551988631700762791734416832, 76224316904413515109600204032, 34239416037606772462135272960, (-12040428054177261698445642240), (-16932642574790452949931617280), 22500808439649071483517598080, 37933994199419171765185807872, 16802355494047963290822708480, 10899060795266658299235069696, 3644662748264676151411196160, 27608407035148989133904206080, (-10631204565854755570641633024)]

private def f404desc6IntegerForm : Matrix (Fin 2) (Fin 2) ℤ :=
  !![52328658590582458137734454962688, 30176798967104178853656364412160;
    30176798967104178853656364412160, 72065285725510126350107464430592]

theorem f404desc6_compression_check :
    f404desc6ᵀ*f410rawM4Form*f404desc6=f404desc6Form := by
  have hD : natFourIntegerMatrix 3 f404desc6IntegerCoordinates=f404desc6 := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix 3 f404desc6IntegerCoordinates) (f404desc6) (by decide +kernel) a b
  have hV : f404desc6IntegerCoordinatesᵀ*f410rawInteger=f404desc6IntegerLeftProduct := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f404desc6IntegerCoordinatesᵀ*f410rawInteger) 0 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f404desc6IntegerLeftProduct) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 23) => (f404desc6IntegerCoordinatesᵀ*f410rawInteger) 1 j)
        (fun (_ : Fin 1) (j : Fin 23) => (f404desc6IntegerLeftProduct) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hY : f404desc6IntegerLeftProduct*f404desc6IntegerCoordinates=f404desc6IntegerForm := by
    ext a b
    fin_cases a
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc6IntegerLeftProduct*f404desc6IntegerCoordinates) 0 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc6IntegerForm) 0 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
    · have h := natFourIntegerEntryCheck_sound
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc6IntegerLeftProduct*f404desc6IntegerCoordinates) 1 j)
        (fun (_ : Fin 1) (j : Fin 2) => (f404desc6IntegerForm) 1 j) (by decide +kernel)
      exact congrFun (congrFun h 0) b
  have hF : natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc6IntegerForm=f404desc6Form := by
    ext a b
    exact natFourRationalEntryCheck_sound (natFourIntegerMatrix (3*1000000000000000000000000*3) f404desc6IntegerForm) (f404desc6Form) (by decide +kernel) a b
  exact natFourIntegerMatrix_compression_check_staged 1000000000000000000000000 3
    f410rawInteger f404desc6IntegerCoordinates f404desc6IntegerLeftProduct f404desc6IntegerForm
    f410rawM4Form f404desc6 f404desc6Form f410_raw_integer_check hD hV hY hF

theorem f404desc6_source_form (x y : Fin 2 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6] (natFourWordBlock f404basis (complexify b404relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6]
          (natFourWordBlock f404basis (complexify b404relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f404desc6Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 6
    f404basis b404relative
    f410basis f404desc6 f410rawM4Form f404desc6Form
    f404desc6_actual f410_actual_raw_M4_matrix f404desc6_compression_check x y


#print axioms f404desc6_compression_check
#print axioms f404desc6_source_form
end TorusLean.BosonFiniteCertificate
