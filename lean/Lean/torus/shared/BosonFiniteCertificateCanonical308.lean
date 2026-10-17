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

theorem k308_family_complex : k308family =
    (fun j => canonicalThreeBlock (factorialScale 8) k308occ k308_particle_degree
      (fun a => complexify b308relative a j)) := by
  rfl
#print axioms k308_family_complex

theorem k308_metric_complex :
    (fun a => (occupationMetricWeight (factorialScale 8) (k308occ a) : ℂ)) =
      (fun a => (k308metric a : ℂ)) := by
  funext a
  exact congrArg (fun q : ℕ => (q : ℂ)) (congrFun k308_metric_reconstructed a)
#print axioms k308_metric_complex

theorem k308_gram_complex_reconstructed : (complexify b308relative)ᴴ *
    Matrix.diagonal (fun a => (k308metric a : ℂ)) * complexify b308relative =
    complexify k308F := by
  have he := congrArg (fun A => complexify A) k308_gram_reconstructed
  simpa only [complexify_mul_rect, complexify_transpose_rect, complexify_diagonal_rat,
    Rat.cast_natCast] using he
#print axioms k308_gram_complex_reconstructed

theorem k308_canonical_gram : familyGram k308family = complexify k308F := by
  calc
    familyGram k308family = familyGram (fun j =>
        canonicalThreeBlock (factorialScale 8) k308occ k308_particle_degree
          (fun a => complexify b308relative a j)) :=
      congrArg familyGram k308_family_complex
    _ = (complexify b308relative)ᴴ * Matrix.diagonal
        (fun a => (occupationMetricWeight (factorialScale 8) (k308occ a) : ℂ)) *
        complexify b308relative :=
      canonicalRelativeFamily_gram (factorialScale 8) k308occ
        k308_occupation_injective k308_particle_degree (complexify b308relative)
    _ = (complexify b308relative)ᴴ * Matrix.diagonal
        (fun a => (k308metric a : ℂ)) * complexify b308relative := by
      rw [k308_metric_complex]
    _ = complexify k308F := k308_gram_complex_reconstructed
#print axioms k308_canonical_gram

theorem k308_inverse_complex_left : complexify k308J * complexify k308F = 1 := by
  rw [← complexify_mul_rect, k308_inverse_left, complexify_one_rat]

theorem k308_inverse_complex_right : complexify k308F * complexify k308J = 1 := by
  rw [← complexify_mul_rect, k308_inverse_right, complexify_one_rat]

theorem k308_inverse_hermitian : (complexify k308J).IsHermitian := by
  rw [Matrix.IsHermitian, ← complexify_transpose_rect, k308_inverse_symmetric]

/-- The concrete Riesz operator of the original-row planar E3 comparison in
its finite relative coordinate block, represented in the canonical N=3 carrier. -/
def k308comparisonOperator : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k308family
    (inverseGramCoefficient (complexify k308J) (complexify c308comparisonRaw))

theorem k308_comparison_operator_form (x y : Fin 2 → ℂ) :
    ip (familySynthesis k308family x).val
      (k308comparisonOperator (familySynthesis k308family y)).val =
      star x ⬝ᵥ (complexify c308comparisonRaw *ᵥ y) := by
  unfold k308comparisonOperator
  exact inverseGramRealization_form k308family (complexify k308F) (complexify k308J)
    (complexify c308comparisonRaw) k308_canonical_gram
    k308_inverse_complex_right k308_inverse_complex_left x y
#print axioms k308_comparison_operator_form

theorem k308_comparison_operator_nonneg (f : ThreeSector (Fin 9)) :
    0 ≤ (ip f.val (k308comparisonOperator f).val).re := by
  unfold k308comparisonOperator
  exact rankOneRealization_nonneg k308family
    (inverseGramCoefficient (complexify k308J) (complexify c308comparisonRaw))
    (inverseGramCoefficient_posSemidef (complexify k308J) (complexify c308comparisonRaw)
      k308_inverse_hermitian
      c308_source_comparison_positive) f
#print axioms k308_comparison_operator_nonneg

theorem k308_comparison_lift_nonneg (f : Core (Fin 9) ℂ) :
    0 ≤ (ip f (threeBodyLift k308comparisonOperator f)).re :=
  threeBodyLift_nonneg k308comparisonOperator k308_comparison_operator_nonneg f

#print axioms k308_canonical_gram
#print axioms k308_comparison_operator_form
#print axioms k308_comparison_operator_nonneg
#print axioms k308_comparison_lift_nonneg

end TorusLean.BosonFiniteCertificate
