import torus.shared.BosonFiniteCertificateNatFourDescendants410P5CompressionTheorem

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f410desc5_source_form (x y : Fin 5 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5] (natFourWordBlock f410basis (complexify b410relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[5]
          (natFourWordBlock f410basis (complexify b410relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f410desc5Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 5
    f410basis b410relative
    f415basis f410desc5 f415rawM4Form f410desc5Form
    f410desc5_actual f415_actual_raw_M4_matrix f410desc5_compression_check x y

#print axioms f410desc5_source_form

end TorusLean.BosonFiniteCertificate
