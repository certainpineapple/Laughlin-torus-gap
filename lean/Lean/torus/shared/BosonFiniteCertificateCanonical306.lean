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

theorem k306_family_complex : k306family =
    (fun j => canonicalThreeBlock (factorialScale 8) k306occ k306_particle_degree
      (fun a => complexify b306relative a j)) := by
  rfl
#print axioms k306_family_complex

theorem k306_metric_complex :
    (fun a => (occupationMetricWeight (factorialScale 8) (k306occ a) : ℂ)) =
      (fun a => (k306metric a : ℂ)) := by
  funext a
  exact congrArg (fun q : ℕ => (q : ℂ)) (congrFun k306_metric_reconstructed a)
#print axioms k306_metric_complex

theorem k306_gram_complex_reconstructed : (complexify b306relative)ᴴ *
    Matrix.diagonal (fun a => (k306metric a : ℂ)) * complexify b306relative =
    complexify k306F := by
  have he := congrArg (fun A => complexify A) k306_gram_reconstructed
  simpa only [complexify_mul_rect, complexify_transpose_rect, complexify_diagonal_rat,
    Rat.cast_natCast] using he
#print axioms k306_gram_complex_reconstructed

theorem k306_canonical_gram : familyGram k306family = complexify k306F := by
  calc
    familyGram k306family = familyGram (fun j =>
        canonicalThreeBlock (factorialScale 8) k306occ k306_particle_degree
          (fun a => complexify b306relative a j)) :=
      congrArg familyGram k306_family_complex
    _ = (complexify b306relative)ᴴ * Matrix.diagonal
        (fun a => (occupationMetricWeight (factorialScale 8) (k306occ a) : ℂ)) *
        complexify b306relative :=
      canonicalRelativeFamily_gram (factorialScale 8) k306occ
        k306_occupation_injective k306_particle_degree (complexify b306relative)
    _ = (complexify b306relative)ᴴ * Matrix.diagonal
        (fun a => (k306metric a : ℂ)) * complexify b306relative := by
      rw [k306_metric_complex]
    _ = complexify k306F := k306_gram_complex_reconstructed
#print axioms k306_canonical_gram

theorem k306_inverse_complex_left : complexify k306J * complexify k306F = 1 := by
  rw [← complexify_mul_rect, k306_inverse_left, complexify_one_rat]

theorem k306_inverse_complex_right : complexify k306F * complexify k306J = 1 := by
  rw [← complexify_mul_rect, k306_inverse_right, complexify_one_rat]

theorem k306_inverse_hermitian : (complexify k306J).IsHermitian := by
  rw [Matrix.IsHermitian, ← complexify_transpose_rect, k306_inverse_symmetric]

/-- The concrete Riesz operator of the original-row planar E3 comparison in
its finite relative coordinate block, represented in the canonical N=3 carrier. -/
def k306comparisonOperator : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k306family
    (inverseGramCoefficient (complexify k306J) (complexify c306comparisonRaw))

theorem k306_comparison_operator_form (x y : Fin 2 → ℂ) :
    ip (familySynthesis k306family x).val
      (k306comparisonOperator (familySynthesis k306family y)).val =
      star x ⬝ᵥ (complexify c306comparisonRaw *ᵥ y) := by
  unfold k306comparisonOperator
  exact inverseGramRealization_form k306family (complexify k306F) (complexify k306J)
    (complexify c306comparisonRaw) k306_canonical_gram
    k306_inverse_complex_right k306_inverse_complex_left x y
#print axioms k306_comparison_operator_form

theorem k306_comparison_operator_nonneg (f : ThreeSector (Fin 9)) :
    0 ≤ (ip f.val (k306comparisonOperator f).val).re := by
  unfold k306comparisonOperator
  exact rankOneRealization_nonneg k306family
    (inverseGramCoefficient (complexify k306J) (complexify c306comparisonRaw))
    (inverseGramCoefficient_posSemidef (complexify k306J) (complexify c306comparisonRaw)
      k306_inverse_hermitian
      c306_source_comparison_positive) f
#print axioms k306_comparison_operator_nonneg

theorem k306_comparison_lift_nonneg (f : Core (Fin 9) ℂ) :
    0 ≤ (ip f (threeBodyLift k306comparisonOperator f)).re :=
  threeBodyLift_nonneg k306comparisonOperator k306_comparison_operator_nonneg f

#print axioms k306_canonical_gram
#print axioms k306_comparison_operator_form
#print axioms k306_comparison_operator_nonneg
#print axioms k306_comparison_lift_nonneg

end TorusLean.BosonFiniteCertificate
