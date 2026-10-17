import torus.shared.BosonFiniteCertificateNatFourDescendants414P0CompressionTheorem
import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f414desc0_source_form (x y : Fin 8 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0] (natFourWordBlock f414basis (complexify b414relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
          (natFourWordBlock f414basis (complexify b414relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f414desc0Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 0
    f414basis b414relative
    f414basis f414desc0 f414rawM4Form f414desc0Form
    f414desc0_actual f414_actual_raw_M4_matrix f414desc0_compression_check x y

#print axioms f414desc0_source_form

end TorusLean.BosonFiniteCertificate
