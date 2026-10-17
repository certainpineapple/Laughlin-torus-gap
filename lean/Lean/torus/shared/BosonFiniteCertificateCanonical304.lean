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

theorem k304_family_complex : k304family =
    (fun j => canonicalThreeBlock (factorialScale 8) k304occ k304_particle_degree
      (fun a => complexify b304relative a j)) := by
  rfl
#print axioms k304_family_complex

theorem k304_metric_complex :
    (fun a => (occupationMetricWeight (factorialScale 8) (k304occ a) : ℂ)) =
      (fun a => (k304metric a : ℂ)) := by
  funext a
  exact congrArg (fun q : ℕ => (q : ℂ)) (congrFun k304_metric_reconstructed a)
#print axioms k304_metric_complex

theorem k304_gram_complex_reconstructed : (complexify b304relative)ᴴ *
    Matrix.diagonal (fun a => (k304metric a : ℂ)) * complexify b304relative =
    complexify k304F := by
  have he := congrArg (fun A => complexify A) k304_gram_reconstructed
  simpa only [complexify_mul_rect, complexify_transpose_rect, complexify_diagonal_rat,
    Rat.cast_natCast] using he
#print axioms k304_gram_complex_reconstructed

theorem k304_canonical_gram : familyGram k304family = complexify k304F := by
  calc
    familyGram k304family = familyGram (fun j =>
        canonicalThreeBlock (factorialScale 8) k304occ k304_particle_degree
          (fun a => complexify b304relative a j)) :=
      congrArg familyGram k304_family_complex
    _ = (complexify b304relative)ᴴ * Matrix.diagonal
        (fun a => (occupationMetricWeight (factorialScale 8) (k304occ a) : ℂ)) *
        complexify b304relative :=
      canonicalRelativeFamily_gram (factorialScale 8) k304occ
        k304_occupation_injective k304_particle_degree (complexify b304relative)
    _ = (complexify b304relative)ᴴ * Matrix.diagonal
        (fun a => (k304metric a : ℂ)) * complexify b304relative := by
      rw [k304_metric_complex]
    _ = complexify k304F := k304_gram_complex_reconstructed
#print axioms k304_canonical_gram

theorem k304_inverse_complex_left : complexify k304J * complexify k304F = 1 := by
  rw [← complexify_mul_rect, k304_inverse_left, complexify_one_rat]

theorem k304_inverse_complex_right : complexify k304F * complexify k304J = 1 := by
  rw [← complexify_mul_rect, k304_inverse_right, complexify_one_rat]

theorem k304_inverse_hermitian : (complexify k304J).IsHermitian := by
  rw [Matrix.IsHermitian, ← complexify_transpose_rect, k304_inverse_symmetric]

/-- The concrete Riesz operator of the original-row planar E3 comparison in
its finite relative coordinate block, represented in the canonical N=3 carrier. -/
def k304comparisonOperator : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k304family
    (inverseGramCoefficient (complexify k304J) (complexify c304comparisonRaw))

theorem k304_comparison_operator_form (x y : Fin 1 → ℂ) :
    ip (familySynthesis k304family x).val
      (k304comparisonOperator (familySynthesis k304family y)).val =
      star x ⬝ᵥ (complexify c304comparisonRaw *ᵥ y) := by
  unfold k304comparisonOperator
  exact inverseGramRealization_form k304family (complexify k304F) (complexify k304J)
    (complexify c304comparisonRaw) k304_canonical_gram
    k304_inverse_complex_right k304_inverse_complex_left x y
#print axioms k304_comparison_operator_form

theorem k304_comparison_operator_nonneg (f : ThreeSector (Fin 9)) :
    0 ≤ (ip f.val (k304comparisonOperator f).val).re := by
  unfold k304comparisonOperator
  exact rankOneRealization_nonneg k304family
    (inverseGramCoefficient (complexify k304J) (complexify c304comparisonRaw))
    (inverseGramCoefficient_posSemidef (complexify k304J) (complexify c304comparisonRaw)
      k304_inverse_hermitian
      c304_source_comparison_positive) f
#print axioms k304_comparison_operator_nonneg

theorem k304_comparison_lift_nonneg (f : Core (Fin 9) ℂ) :
    0 ≤ (ip f (threeBodyLift k304comparisonOperator f)).re :=
  threeBodyLift_nonneg k304comparisonOperator k304_comparison_operator_nonneg f

#print axioms k304_canonical_gram
#print axioms k304_comparison_operator_form
#print axioms k304_comparison_operator_nonneg
#print axioms k304_comparison_lift_nonneg

end TorusLean.BosonFiniteCertificate
