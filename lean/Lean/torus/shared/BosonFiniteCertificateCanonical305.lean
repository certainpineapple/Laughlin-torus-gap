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

theorem k305_family_complex : k305family =
    (fun j => canonicalThreeBlock (factorialScale 8) k305occ k305_particle_degree
      (fun a => complexify b305relative a j)) := by
  rfl
#print axioms k305_family_complex

theorem k305_metric_complex :
    (fun a => (occupationMetricWeight (factorialScale 8) (k305occ a) : ℂ)) =
      (fun a => (k305metric a : ℂ)) := by
  funext a
  exact congrArg (fun q : ℕ => (q : ℂ)) (congrFun k305_metric_reconstructed a)
#print axioms k305_metric_complex

theorem k305_gram_complex_reconstructed : (complexify b305relative)ᴴ *
    Matrix.diagonal (fun a => (k305metric a : ℂ)) * complexify b305relative =
    complexify k305F := by
  have he := congrArg (fun A => complexify A) k305_gram_reconstructed
  simpa only [complexify_mul_rect, complexify_transpose_rect, complexify_diagonal_rat,
    Rat.cast_natCast] using he
#print axioms k305_gram_complex_reconstructed

theorem k305_canonical_gram : familyGram k305family = complexify k305F := by
  calc
    familyGram k305family = familyGram (fun j =>
        canonicalThreeBlock (factorialScale 8) k305occ k305_particle_degree
          (fun a => complexify b305relative a j)) :=
      congrArg familyGram k305_family_complex
    _ = (complexify b305relative)ᴴ * Matrix.diagonal
        (fun a => (occupationMetricWeight (factorialScale 8) (k305occ a) : ℂ)) *
        complexify b305relative :=
      canonicalRelativeFamily_gram (factorialScale 8) k305occ
        k305_occupation_injective k305_particle_degree (complexify b305relative)
    _ = (complexify b305relative)ᴴ * Matrix.diagonal
        (fun a => (k305metric a : ℂ)) * complexify b305relative := by
      rw [k305_metric_complex]
    _ = complexify k305F := k305_gram_complex_reconstructed
#print axioms k305_canonical_gram

theorem k305_inverse_complex_left : complexify k305J * complexify k305F = 1 := by
  rw [← complexify_mul_rect, k305_inverse_left, complexify_one_rat]

theorem k305_inverse_complex_right : complexify k305F * complexify k305J = 1 := by
  rw [← complexify_mul_rect, k305_inverse_right, complexify_one_rat]

theorem k305_inverse_hermitian : (complexify k305J).IsHermitian := by
  rw [Matrix.IsHermitian, ← complexify_transpose_rect, k305_inverse_symmetric]

/-- The concrete Riesz operator of the original-row planar E3 comparison in
its finite relative coordinate block, represented in the canonical N=3 carrier. -/
def k305comparisonOperator : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k305family
    (inverseGramCoefficient (complexify k305J) (complexify c305comparisonRaw))

theorem k305_comparison_operator_form (x y : Fin 1 → ℂ) :
    ip (familySynthesis k305family x).val
      (k305comparisonOperator (familySynthesis k305family y)).val =
      star x ⬝ᵥ (complexify c305comparisonRaw *ᵥ y) := by
  unfold k305comparisonOperator
  exact inverseGramRealization_form k305family (complexify k305F) (complexify k305J)
    (complexify c305comparisonRaw) k305_canonical_gram
    k305_inverse_complex_right k305_inverse_complex_left x y
#print axioms k305_comparison_operator_form

theorem k305_comparison_operator_nonneg (f : ThreeSector (Fin 9)) :
    0 ≤ (ip f.val (k305comparisonOperator f).val).re := by
  unfold k305comparisonOperator
  exact rankOneRealization_nonneg k305family
    (inverseGramCoefficient (complexify k305J) (complexify c305comparisonRaw))
    (inverseGramCoefficient_posSemidef (complexify k305J) (complexify c305comparisonRaw)
      k305_inverse_hermitian
      c305_source_comparison_positive) f
#print axioms k305_comparison_operator_nonneg

theorem k305_comparison_lift_nonneg (f : Core (Fin 9) ℂ) :
    0 ≤ (ip f (threeBodyLift k305comparisonOperator f)).re :=
  threeBodyLift_nonneg k305comparisonOperator k305_comparison_operator_nonneg f

#print axioms k305_canonical_gram
#print axioms k305_comparison_operator_form
#print axioms k305_comparison_operator_nonneg
#print axioms k305_comparison_lift_nonneg

end TorusLean.BosonFiniteCertificate
