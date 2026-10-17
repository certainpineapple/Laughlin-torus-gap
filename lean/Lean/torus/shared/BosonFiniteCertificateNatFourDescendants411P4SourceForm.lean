import torus.shared.BosonFiniteCertificateNatFourDescendants411P4CompressionTheorem
import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f411desc4_source_form (x y : Fin 4 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4] (natFourWordBlock f411basis (complexify b411relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[4]
          (natFourWordBlock f411basis (complexify b411relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f411desc4Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 4
    f411basis b411relative
    f415basis f411desc4 f415rawM4Form f411desc4Form
    f411desc4_actual f415_actual_raw_M4_matrix f411desc4_compression_check x y

#print axioms f411desc4_source_form

end TorusLean.BosonFiniteCertificate
