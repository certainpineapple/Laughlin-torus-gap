import torus.shared.BosonFiniteCertificateCanonicalData
import torus.shared.BosonFiniteCertificateCanonicalGram
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Matrix
open scoped BigOperators ComplexOrder
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.M2
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonThreeBodyLift
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonFiniteCertificateRealization

theorem k302_family_complex : k302family =
    (fun j => canonicalThreeBlock (factorialScale 8) k302occ k302_particle_degree
      (fun a => complexify b302relative a j)) := by
  rfl
#print axioms k302_family_complex

theorem k302_metric_complex :
    (fun a => (occupationMetricWeight (factorialScale 8) (k302occ a) : ℂ)) =
      (fun a => (k302metric a : ℂ)) := by
  funext a
  exact congrArg (fun q : ℕ => (q : ℂ)) (congrFun k302_metric_reconstructed a)
#print axioms k302_metric_complex

theorem k302_gram_complex_reconstructed : (complexify b302relative)ᴴ *
    Matrix.diagonal (fun a => (k302metric a : ℂ)) * complexify b302relative =
    complexify k302F := by
  have he := congrArg (fun A => complexify A) k302_gram_reconstructed
  simpa only [complexify_mul_rect, complexify_transpose_rect, complexify_diagonal_rat,
    Rat.cast_natCast] using he
#print axioms k302_gram_complex_reconstructed

theorem k302_canonical_gram : familyGram k302family = complexify k302F := by
  calc
    familyGram k302family = familyGram (fun j =>
        canonicalThreeBlock (factorialScale 8) k302occ k302_particle_degree
          (fun a => complexify b302relative a j)) :=
      congrArg familyGram k302_family_complex
    _ = (complexify b302relative)ᴴ * Matrix.diagonal
        (fun a => (occupationMetricWeight (factorialScale 8) (k302occ a) : ℂ)) *
        complexify b302relative :=
      canonicalRelativeFamily_gram (factorialScale 8) k302occ
        k302_occupation_injective k302_particle_degree (complexify b302relative)
    _ = (complexify b302relative)ᴴ * Matrix.diagonal
        (fun a => (k302metric a : ℂ)) * complexify b302relative := by
      rw [k302_metric_complex]
    _ = complexify k302F := k302_gram_complex_reconstructed
#print axioms k302_canonical_gram

theorem k302_inverse_complex_left : complexify k302J * complexify k302F = 1 := by
  rw [← complexify_mul_rect, k302_inverse_left, complexify_one_rat]

theorem k302_inverse_complex_right : complexify k302F * complexify k302J = 1 := by
  rw [← complexify_mul_rect, k302_inverse_right, complexify_one_rat]

theorem k302_inverse_hermitian : (complexify k302J).IsHermitian := by
  rw [Matrix.IsHermitian, ← complexify_transpose_rect, k302_inverse_symmetric]

/-- The concrete Riesz operator of the original-row planar E3 comparison in
its finite relative coordinate block, represented in the canonical N=3 carrier. -/
def k302comparisonOperator : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k302family
    (inverseGramCoefficient (complexify k302J) (complexify c302comparisonRaw))

theorem k302_comparison_operator_form (x y : Fin 1 → ℂ) :
    ip (familySynthesis k302family x).val
      (k302comparisonOperator (familySynthesis k302family y)).val =
      star x ⬝ᵥ (complexify c302comparisonRaw *ᵥ y) := by
  unfold k302comparisonOperator
  exact inverseGramRealization_form k302family (complexify k302F) (complexify k302J)
    (complexify c302comparisonRaw) k302_canonical_gram
    k302_inverse_complex_right k302_inverse_complex_left x y
#print axioms k302_comparison_operator_form

theorem k302_comparison_operator_nonneg (f : ThreeSector (Fin 9)) :
    0 ≤ (ip f.val (k302comparisonOperator f).val).re := by
  unfold k302comparisonOperator
  exact rankOneRealization_nonneg k302family
    (inverseGramCoefficient (complexify k302J) (complexify c302comparisonRaw))
    (inverseGramCoefficient_posSemidef (complexify k302J) (complexify c302comparisonRaw)
      k302_inverse_hermitian
      c302_source_comparison_positive) f
#print axioms k302_comparison_operator_nonneg

theorem k302_comparison_lift_nonneg (f : Core (Fin 9) ℂ) :
    0 ≤ (ip f (threeBodyLift k302comparisonOperator f)).re :=
  threeBodyLift_nonneg k302comparisonOperator k302_comparison_operator_nonneg f

#print axioms k302_canonical_gram
#print axioms k302_comparison_operator_form
#print axioms k302_comparison_operator_nonneg
#print axioms k302_comparison_lift_nonneg

end TorusLean.BosonFiniteCertificate
