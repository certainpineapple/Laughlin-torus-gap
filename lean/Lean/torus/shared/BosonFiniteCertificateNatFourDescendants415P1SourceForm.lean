import torus.shared.BosonFiniteCertificateNatFourDescendants415P1CompressionTheorem
import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f415desc1_source_form (x y : Fin 7 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1] (natFourWordBlock f415basis (complexify b415relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
          (natFourWordBlock f415basis (complexify b415relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f415desc1Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 1
    f415basis b415relative
    f416basis f415desc1 f416rawM4Form f415desc1Form
    f415desc1_actual f416_actual_raw_M4_matrix f415desc1_compression_check x y

#print axioms f415desc1_source_form

end TorusLean.BosonFiniteCertificate
