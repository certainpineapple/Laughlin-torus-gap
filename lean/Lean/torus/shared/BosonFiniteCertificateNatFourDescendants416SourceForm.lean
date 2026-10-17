import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit
import torus.shared.BosonFiniteCertificateNatFourDescendants416CompressionTheorem

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

theorem f416desc0_source_form (x y : Fin 10 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0] (natFourWordBlock f416basis (complexify b416relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
          (natFourWordBlock f416basis (complexify b416relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f416desc0Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 0
    f416basis b416relative
    f416basis f416desc0 f416rawM4Form f416desc0Form
    f416desc0_actual f416_actual_raw_M4_matrix f416desc0_compression_check x y

#print axioms f416desc0_source_form
end TorusLean.BosonFiniteCertificate
