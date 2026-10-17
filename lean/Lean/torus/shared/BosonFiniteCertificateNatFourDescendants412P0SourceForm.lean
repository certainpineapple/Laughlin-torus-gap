import torus.shared.BosonFiniteCertificateNatFourDescendants412P0CompressionTheorem
import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f412desc0_source_form (x y : Fin 7 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0] (natFourWordBlock f412basis (complexify b412relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
          (natFourWordBlock f412basis (complexify b412relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f412desc0Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 0
    f412basis b412relative
    f412basis f412desc0 f412rawM4Form f412desc0Form
    f412desc0_actual f412_actual_raw_M4_matrix f412desc0_compression_check x y

#print axioms f412desc0_source_form

end TorusLean.BosonFiniteCertificate
