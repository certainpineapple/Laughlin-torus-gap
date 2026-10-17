import torus.shared.BosonFiniteCertificateNatFourDescendants411P5CompressionTheorem
import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f411desc5_source_form (x y : Fin 4 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5] (natFourWordBlock f411basis (complexify b411relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
          (natFourWordBlock f411basis (complexify b411relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f411desc5Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 5
    f411basis b411relative
    f416basis f411desc5 f416rawM4Form f411desc5Form
    f411desc5_actual f416_actual_raw_M4_matrix f411desc5_compression_check x y

#print axioms f411desc5_source_form

end TorusLean.BosonFiniteCertificate
