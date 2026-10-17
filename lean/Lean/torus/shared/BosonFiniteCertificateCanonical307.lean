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

theorem k307_family_complex : k307family =
    (fun j => canonicalThreeBlock (factorialScale 8) k307occ k307_particle_degree
      (fun a => complexify b307relative a j)) := by
  rfl
#print axioms k307_family_complex

theorem k307_metric_complex :
    (fun a => (occupationMetricWeight (factorialScale 8) (k307occ a) : ℂ)) =
      (fun a => (k307metric a : ℂ)) := by
  funext a
  exact congrArg (fun q : ℕ => (q : ℂ)) (congrFun k307_metric_reconstructed a)
#print axioms k307_metric_complex

theorem k307_gram_complex_reconstructed : (complexify b307relative)ᴴ *
    Matrix.diagonal (fun a => (k307metric a : ℂ)) * complexify b307relative =
    complexify k307F := by
  have he := congrArg (fun A => complexify A) k307_gram_reconstructed
  simpa only [complexify_mul_rect, complexify_transpose_rect, complexify_diagonal_rat,
    Rat.cast_natCast] using he
#print axioms k307_gram_complex_reconstructed

theorem k307_canonical_gram : familyGram k307family = complexify k307F := by
  calc
    familyGram k307family = familyGram (fun j =>
        canonicalThreeBlock (factorialScale 8) k307occ k307_particle_degree
          (fun a => complexify b307relative a j)) :=
      congrArg familyGram k307_family_complex
    _ = (complexify b307relative)ᴴ * Matrix.diagonal
        (fun a => (occupationMetricWeight (factorialScale 8) (k307occ a) : ℂ)) *
        complexify b307relative :=
      canonicalRelativeFamily_gram (factorialScale 8) k307occ
        k307_occupation_injective k307_particle_degree (complexify b307relative)
    _ = (complexify b307relative)ᴴ * Matrix.diagonal
        (fun a => (k307metric a : ℂ)) * complexify b307relative := by
      rw [k307_metric_complex]
    _ = complexify k307F := k307_gram_complex_reconstructed
#print axioms k307_canonical_gram

theorem k307_inverse_complex_left : complexify k307J * complexify k307F = 1 := by
  rw [← complexify_mul_rect, k307_inverse_left, complexify_one_rat]

theorem k307_inverse_complex_right : complexify k307F * complexify k307J = 1 := by
  rw [← complexify_mul_rect, k307_inverse_right, complexify_one_rat]

theorem k307_inverse_hermitian : (complexify k307J).IsHermitian := by
  rw [Matrix.IsHermitian, ← complexify_transpose_rect, k307_inverse_symmetric]

/-- The concrete Riesz operator of the original-row planar E3 comparison in
its finite relative coordinate block, represented in the canonical N=3 carrier. -/
def k307comparisonOperator : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k307family
    (inverseGramCoefficient (complexify k307J) (complexify c307comparisonRaw))

theorem k307_comparison_operator_form (x y : Fin 1 → ℂ) :
    ip (familySynthesis k307family x).val
      (k307comparisonOperator (familySynthesis k307family y)).val =
      star x ⬝ᵥ (complexify c307comparisonRaw *ᵥ y) := by
  unfold k307comparisonOperator
  exact inverseGramRealization_form k307family (complexify k307F) (complexify k307J)
    (complexify c307comparisonRaw) k307_canonical_gram
    k307_inverse_complex_right k307_inverse_complex_left x y
#print axioms k307_comparison_operator_form

theorem k307_comparison_operator_nonneg (f : ThreeSector (Fin 9)) :
    0 ≤ (ip f.val (k307comparisonOperator f).val).re := by
  unfold k307comparisonOperator
  exact rankOneRealization_nonneg k307family
    (inverseGramCoefficient (complexify k307J) (complexify c307comparisonRaw))
    (inverseGramCoefficient_posSemidef (complexify k307J) (complexify c307comparisonRaw)
      k307_inverse_hermitian
      c307_source_comparison_positive) f
#print axioms k307_comparison_operator_nonneg

theorem k307_comparison_lift_nonneg (f : Core (Fin 9) ℂ) :
    0 ≤ (ip f (threeBodyLift k307comparisonOperator f)).re :=
  threeBodyLift_nonneg k307comparisonOperator k307_comparison_operator_nonneg f

#print axioms k307_canonical_gram
#print axioms k307_comparison_operator_form
#print axioms k307_comparison_operator_nonneg
#print axioms k307_comparison_lift_nonneg

end TorusLean.BosonFiniteCertificate
