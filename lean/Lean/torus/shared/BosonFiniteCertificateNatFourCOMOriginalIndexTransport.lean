import torus.shared.BosonFiniteCertificateNatFourCOMOriginalFormTransport

/-! Explicit index equality is transported before the original source form is
instantiated, so dependent dimension reduction stays outside the operator. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

theorem natFourRawMatrixForm_transportIndex {n m : ℕ} (e : n=m)
    (b₁ : Fin n → List ℕ) (b₂ : Fin m → List ℕ)
    (M₁ : Matrix (Fin n) (Fin n) ℚ) (M₂ : Matrix (Fin m) (Fin m) ℚ)
    (hb : b₁=(fun i => b₂ (Fin.cast e i)))
    (hM : M₁=(fun i j => M₂ (Fin.cast e i) (Fin.cast e j)))
    (h : ∀ x y : Fin m → ℂ,
      natOccupationInner (natFourWordBlock b₂ x)
        (canonicalNatFourOriginalOperator (natFourWordBlock b₂ y))=
          star x ⬝ᵥ (complexify M₂ *ᵥ y))
    (x y : Fin n → ℂ) :
    natOccupationInner (natFourWordBlock b₁ x)
      (canonicalNatFourOriginalOperator (natFourWordBlock b₁ y))=
        star x ⬝ᵥ (complexify M₁ *ᵥ y) := by
  cases e
  have hb' : b₁=b₂ := by simpa only [Fin.cast_refl, id_eq] using hb
  have hM' : M₁=M₂ := by simpa only [Fin.cast_refl, id_eq] using hM
  exact natFourRawMatrixForm_transport b₁ b₂ M₁ M₂ hb' hM' h x y

#print axioms natFourRawMatrixForm_transportIndex
end TorusLean.BosonFiniteCertificate
