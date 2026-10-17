import torus.shared.BosonFiniteCertificateNatFourDescendants410P6CompressionTheorem

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f410desc6_source_form (x y : Fin 5 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6] (natFourWordBlock f410basis (complexify b410relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[6]
          (natFourWordBlock f410basis (complexify b410relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f410desc6Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 6
    f410basis b410relative
    f416basis f410desc6 f416rawM4Form f410desc6Form
    f410desc6_actual f416_actual_raw_M4_matrix f410desc6_compression_check x y

#print axioms f410desc6_source_form

end TorusLean.BosonFiniteCertificate
