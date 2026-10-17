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

theorem k300_family_complex : k300family =
    (fun j => canonicalThreeBlock (factorialScale 8) k300occ k300_particle_degree
      (fun a => complexify b300relative a j)) := by
  rfl
#print axioms k300_family_complex

theorem k300_metric_complex :
    (fun a => (occupationMetricWeight (factorialScale 8) (k300occ a) : ℂ)) =
      (fun a => (k300metric a : ℂ)) := by
  funext a
  exact congrArg (fun q : ℕ => (q : ℂ)) (congrFun k300_metric_reconstructed a)
#print axioms k300_metric_complex

theorem k300_gram_complex_reconstructed : (complexify b300relative)ᴴ *
    Matrix.diagonal (fun a => (k300metric a : ℂ)) * complexify b300relative =
    complexify k300F := by
  have he := congrArg (fun A => complexify A) k300_gram_reconstructed
  simpa only [complexify_mul_rect, complexify_transpose_rect, complexify_diagonal_rat,
    Rat.cast_natCast] using he
#print axioms k300_gram_complex_reconstructed

theorem k300_canonical_gram : familyGram k300family = complexify k300F := by
  calc
    familyGram k300family = familyGram (fun j =>
        canonicalThreeBlock (factorialScale 8) k300occ k300_particle_degree
          (fun a => complexify b300relative a j)) :=
      congrArg familyGram k300_family_complex
    _ = (complexify b300relative)ᴴ * Matrix.diagonal
        (fun a => (occupationMetricWeight (factorialScale 8) (k300occ a) : ℂ)) *
        complexify b300relative :=
      canonicalRelativeFamily_gram (factorialScale 8) k300occ
        k300_occupation_injective k300_particle_degree (complexify b300relative)
    _ = (complexify b300relative)ᴴ * Matrix.diagonal
        (fun a => (k300metric a : ℂ)) * complexify b300relative := by
      rw [k300_metric_complex]
    _ = complexify k300F := k300_gram_complex_reconstructed
#print axioms k300_canonical_gram

theorem k300_inverse_complex_left : complexify k300J * complexify k300F = 1 := by
  rw [← complexify_mul_rect, k300_inverse_left, complexify_one_rat]

theorem k300_inverse_complex_right : complexify k300F * complexify k300J = 1 := by
  rw [← complexify_mul_rect, k300_inverse_right, complexify_one_rat]

theorem k300_inverse_hermitian : (complexify k300J).IsHermitian := by
  rw [Matrix.IsHermitian, ← complexify_transpose_rect, k300_inverse_symmetric]

/-- The concrete Riesz operator of the original-row planar E3 comparison in
its finite relative coordinate block, represented in the canonical N=3 carrier. -/
def k300comparisonOperator : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k300family
    (inverseGramCoefficient (complexify k300J) (complexify c300comparisonRaw))

theorem k300_comparison_operator_form (x y : Fin 1 → ℂ) :
    ip (familySynthesis k300family x).val
      (k300comparisonOperator (familySynthesis k300family y)).val =
      star x ⬝ᵥ (complexify c300comparisonRaw *ᵥ y) := by
  unfold k300comparisonOperator
  exact inverseGramRealization_form k300family (complexify k300F) (complexify k300J)
    (complexify c300comparisonRaw) k300_canonical_gram
    k300_inverse_complex_right k300_inverse_complex_left x y
#print axioms k300_comparison_operator_form

theorem k300_comparison_operator_nonneg (f : ThreeSector (Fin 9)) :
    0 ≤ (ip f.val (k300comparisonOperator f).val).re := by
  unfold k300comparisonOperator
  exact rankOneRealization_nonneg k300family
    (inverseGramCoefficient (complexify k300J) (complexify c300comparisonRaw))
    (inverseGramCoefficient_posSemidef (complexify k300J) (complexify c300comparisonRaw)
      k300_inverse_hermitian
      c300_source_comparison_positive) f
#print axioms k300_comparison_operator_nonneg

theorem k300_comparison_lift_nonneg (f : Core (Fin 9) ℂ) :
    0 ≤ (ip f (threeBodyLift k300comparisonOperator f)).re :=
  threeBodyLift_nonneg k300comparisonOperator k300_comparison_operator_nonneg f

#print axioms k300_canonical_gram
#print axioms k300_comparison_operator_form
#print axioms k300_comparison_operator_nonneg
#print axioms k300_comparison_lift_nonneg

end TorusLean.BosonFiniteCertificate
