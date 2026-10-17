import torus.shared.BosonFiniteCertificateNatFourDescendants411P0CompressionTheorem
import torus.shared.BosonFiniteCertificateNatFourDescendantSourceExplicit

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2 Matrix
open scoped BigOperators

theorem f411desc0_source_form (x y : Fin 4 → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0] (natFourWordBlock f411basis (complexify b411relative *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[0]
          (natFourWordBlock f411basis (complexify b411relative *ᵥ y))))=
      star x ⬝ᵥ (complexify f411desc0Form *ᵥ y) := by
  exact natFour_descendant_source_form_explicit 0
    f411basis b411relative
    f411basis f411desc0 f411rawM4Form f411desc0Form
    f411desc0_actual f411_actual_raw_M4_matrix f411desc0_compression_check x y

#print axioms f411desc0_source_form

end TorusLean.BosonFiniteCertificate
