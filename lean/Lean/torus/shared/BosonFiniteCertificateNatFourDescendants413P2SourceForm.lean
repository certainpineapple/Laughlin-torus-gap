import torus.shared.BosonFiniteCertificateNatFourDescendants413P2CompressionTheorem
import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f413desc2_source_form (x y : Fin 5 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2] (natFourWordBlock f413basis (complexify b413relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
          (natFourWordBlock f413basis (complexify b413relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f413desc2Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 2
    f413basis b413relative
    f415basis f413desc2 f415rawM4Form f413desc2Form
    f413desc2_actual f415_actual_raw_M4_matrix f413desc2_compression_check x y

#print axioms f413desc2_source_form

end TorusLean.BosonFiniteCertificate
