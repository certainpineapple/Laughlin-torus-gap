import torus.shared.BosonFiniteCertificateNatFourCOMOriginalSourceData

/-! All seventeen separately checked original M4 form matrices enter the
whole-N4, all-COM-level rank expansion. This is an identity of the original
normal-ordered source, not a definition of a candidate matrix operator. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

theorem natFourRawMatrixForm_transport {n : ℕ}
    (b₁ b₂ : Fin n → List ℕ)
    (M₁ M₂ : Matrix (Fin n) (Fin n) ℚ)
    (hb : b₁=b₂) (hM : M₁=M₂)
    (h : ∀ x y : Fin n → ℂ,
      natOccupationInner (natFourWordBlock b₂ x)
        (canonicalNatFourOriginalOperator (natFourWordBlock b₂ y))=
          star x ⬝ᵥ (complexify M₂ *ᵥ y))
    (x y : Fin n → ℂ) :
    natOccupationInner (natFourWordBlock b₁ x)
      (canonicalNatFourOriginalOperator (natFourWordBlock b₁ y))=
        star x ⬝ᵥ (complexify M₁ *ᵥ y) := by
  cases hb
  cases hM
  exact h x y

#print axioms natFourRawMatrixForm_transport
end TorusLean.BosonFiniteCertificate
