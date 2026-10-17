import torus.shared.BosonFiniteCertificateNatFourDescendants415P0CompressionTheorem
import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f415desc0_source_form (x y : Fin 7 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0] (natFourWordBlock f415basis (complexify b415relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
          (natFourWordBlock f415basis (complexify b415relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f415desc0Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 0
    f415basis b415relative
    f415basis f415desc0 f415rawM4Form f415desc0Form
    f415desc0_actual f415_actual_raw_M4_matrix f415desc0_compression_check x y

#print axioms f415desc0_source_form

end TorusLean.BosonFiniteCertificate
