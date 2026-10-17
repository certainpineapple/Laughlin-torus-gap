import torus.shared.BosonFiniteCertificateNatFourDescendants413P3CompressionTheorem
import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413desc3_source_form (x y : Fin 5 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3] (natFourWordBlock f413basis (complexify b413relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[3]
          (natFourWordBlock f413basis (complexify b413relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f413desc3Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 3
    f413basis b413relative
    f416basis f413desc3 f416rawM4Form f413desc3Form
    f413desc3_actual f416_actual_raw_M4_matrix f413desc3_compression_check x y

#print axioms f413desc3_source_form

end TorusLean.BosonFiniteCertificate
