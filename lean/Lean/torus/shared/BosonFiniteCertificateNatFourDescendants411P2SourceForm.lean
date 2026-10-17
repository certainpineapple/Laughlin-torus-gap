import torus.shared.BosonFiniteCertificateNatFourDescendants411P2CompressionTheorem
import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f411desc2_source_form (x y : Fin 4 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2] (natFourWordBlock f411basis (complexify b411relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[2]
          (natFourWordBlock f411basis (complexify b411relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f411desc2Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 2
    f411basis b411relative
    f413basis f411desc2 f413rawM4Form f411desc2Form
    f411desc2_actual f413_actual_raw_M4_matrix f411desc2_compression_check x y

#print axioms f411desc2_source_form

end TorusLean.BosonFiniteCertificate
