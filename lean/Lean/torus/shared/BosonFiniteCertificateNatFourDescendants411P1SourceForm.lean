import torus.shared.BosonFiniteCertificateNatFourDescendants411P1CompressionTheorem
import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f411desc1_source_form (x y : Fin 4 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1] (natFourWordBlock f411basis (complexify b411relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[1]
          (natFourWordBlock f411basis (complexify b411relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f411desc1Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 1
    f411basis b411relative
    f412basis f411desc1 f412rawM4Form f411desc1Form
    f411desc1_actual f412_actual_raw_M4_matrix f411desc1_compression_check x y

#print axioms f411desc1_source_form

end TorusLean.BosonFiniteCertificate
