import torus.shared.BosonFiniteCertificateNatFourDescendantCore

/-! A source-explicit form of the genuine descendant compression theorem.
All actual basis and coordinate parameters occur verbatim on both sides of
the source premise and conclusion, outside the original operator's coercion. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson TorusLean.M2
open Matrix
open scoped BigOperators

theorem natFour_descendant_source_form_explicit {r n₀ n : ℕ} (k : ℕ)
    (basis₀ : Fin n₀ → List ℕ) (C : Matrix (Fin n₀) (Fin r) ℚ)
    (basis : Fin n → List ℕ) (D : Matrix (Fin n) (Fin r) ℚ)
    (M : Matrix (Fin n) (Fin n) ℚ) (F : Matrix (Fin r) (Fin r) ℚ)
    (hD : ∀ x : Fin r → ℂ,
      (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k]
        (natFourWordBlock basis₀ (complexify C *ᵥ x))=
      natFourWordBlock basis (complexify D *ᵥ x))
    (hM : ∀ x y : Fin n → ℂ,
      natOccupationInner (natFourWordBlock basis x)
        (canonicalNatFourOriginalOperator (natFourWordBlock basis y))=
      star x ⬝ᵥ (complexify M *ᵥ y))
    (hF : Dᵀ*M*D=F) (x y : Fin r → ℂ) :
    natOccupationInner
      ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k]
        (natFourWordBlock basis₀ (complexify C *ᵥ x)))
      (canonicalNatFourOriginalOperator
        ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k]
          (natFourWordBlock basis₀ (complexify C *ᵥ y))))=
      star x ⬝ᵥ (complexify F *ᵥ y) := by
  calc
    _ = natOccupationInner (natFourWordBlock basis (complexify D *ᵥ x))
        (canonicalNatFourOriginalOperator
          (natFourWordBlock basis (complexify D *ᵥ y))) :=
      congrArg₂ natOccupationInner (hD x)
        (congrArg (canonicalNatFourOriginalOperator : Core ℕ ℂ → Core ℕ ℂ) (hD y))
    _ = star (complexify D *ᵥ x) ⬝ᵥ
        (complexify M *ᵥ (complexify D *ᵥ y)) :=
      hM (complexify D *ᵥ x) (complexify D *ᵥ y)
    _ = _ := by
      rw [matrixCross_congruence,← complexify_transpose_rect,
        ← complexify_mul_rect,← complexify_mul_rect,hF]

#print axioms natFour_descendant_source_form_explicit
end TorusLean.BosonFiniteCertificate
