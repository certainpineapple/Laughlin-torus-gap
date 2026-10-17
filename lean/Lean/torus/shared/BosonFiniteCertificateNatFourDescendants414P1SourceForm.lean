import torus.shared.BosonFiniteCertificateNatFourDescendants414P1CompressionTheorem
import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f414desc1_source_form (x y : Fin 8 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1] (natFourWordBlock f414basis (complexify b414relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
          (natFourWordBlock f414basis (complexify b414relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f414desc1Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 1
    f414basis b414relative
    f415basis f414desc1 f415rawM4Form f414desc1Form
    f414desc1_actual f415_actual_raw_M4_matrix f414desc1_compression_check x y

#print axioms f414desc1_source_form

end TorusLean.BosonFiniteCertificate
