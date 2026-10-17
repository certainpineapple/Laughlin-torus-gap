import torus.shared.BosonFiniteCertificateNatFourDescendants413P0CompressionTheorem
import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413desc0_source_form (x y : Fin 5 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0] (natFourWordBlock f413basis (complexify b413relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
          (natFourWordBlock f413basis (complexify b413relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f413desc0Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 0
    f413basis b413relative
    f413basis f413desc0 f413rawM4Form f413desc0Form
    f413desc0_actual f413_actual_raw_M4_matrix f413desc0_compression_check x y

#print axioms f413desc0_source_form

end TorusLean.BosonFiniteCertificate
