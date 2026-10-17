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

theorem k303_family_complex : k303family =
    (fun j => canonicalThreeBlock (factorialScale 8) k303occ k303_particle_degree
      (fun a => complexify b303relative a j)) := by
  rfl
#print axioms k303_family_complex

theorem k303_metric_complex :
    (fun a => (occupationMetricWeight (factorialScale 8) (k303occ a) : ℂ)) =
      (fun a => (k303metric a : ℂ)) := by
  funext a
  exact congrArg (fun q : ℕ => (q : ℂ)) (congrFun k303_metric_reconstructed a)
#print axioms k303_metric_complex

theorem k303_gram_complex_reconstructed : (complexify b303relative)ᴴ *
    Matrix.diagonal (fun a => (k303metric a : ℂ)) * complexify b303relative =
    complexify k303F := by
  have he := congrArg (fun A => complexify A) k303_gram_reconstructed
  simpa only [complexify_mul_rect, complexify_transpose_rect, complexify_diagonal_rat,
    Rat.cast_natCast] using he
#print axioms k303_gram_complex_reconstructed

theorem k303_canonical_gram : familyGram k303family = complexify k303F := by
  calc
    familyGram k303family = familyGram (fun j =>
        canonicalThreeBlock (factorialScale 8) k303occ k303_particle_degree
          (fun a => complexify b303relative a j)) :=
      congrArg familyGram k303_family_complex
    _ = (complexify b303relative)ᴴ * Matrix.diagonal
        (fun a => (occupationMetricWeight (factorialScale 8) (k303occ a) : ℂ)) *
        complexify b303relative :=
      canonicalRelativeFamily_gram (factorialScale 8) k303occ
        k303_occupation_injective k303_particle_degree (complexify b303relative)
    _ = (complexify b303relative)ᴴ * Matrix.diagonal
        (fun a => (k303metric a : ℂ)) * complexify b303relative := by
      rw [k303_metric_complex]
    _ = complexify k303F := k303_gram_complex_reconstructed
#print axioms k303_canonical_gram

theorem k303_inverse_complex_left : complexify k303J * complexify k303F = 1 := by
  rw [← complexify_mul_rect, k303_inverse_left, complexify_one_rat]

theorem k303_inverse_complex_right : complexify k303F * complexify k303J = 1 := by
  rw [← complexify_mul_rect, k303_inverse_right, complexify_one_rat]

theorem k303_inverse_hermitian : (complexify k303J).IsHermitian := by
  rw [Matrix.IsHermitian, ← complexify_transpose_rect, k303_inverse_symmetric]

/-- The concrete Riesz operator of the original-row planar E3 comparison in
its finite relative coordinate block, represented in the canonical N=3 carrier. -/
def k303comparisonOperator : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k303family
    (inverseGramCoefficient (complexify k303J) (complexify c303comparisonRaw))

theorem k303_comparison_operator_form (x y : Fin 1 → ℂ) :
    ip (familySynthesis k303family x).val
      (k303comparisonOperator (familySynthesis k303family y)).val =
      star x ⬝ᵥ (complexify c303comparisonRaw *ᵥ y) := by
  unfold k303comparisonOperator
  exact inverseGramRealization_form k303family (complexify k303F) (complexify k303J)
    (complexify c303comparisonRaw) k303_canonical_gram
    k303_inverse_complex_right k303_inverse_complex_left x y
#print axioms k303_comparison_operator_form

theorem k303_comparison_operator_nonneg (f : ThreeSector (Fin 9)) :
    0 ≤ (ip f.val (k303comparisonOperator f).val).re := by
  unfold k303comparisonOperator
  exact rankOneRealization_nonneg k303family
    (inverseGramCoefficient (complexify k303J) (complexify c303comparisonRaw))
    (inverseGramCoefficient_posSemidef (complexify k303J) (complexify c303comparisonRaw)
      k303_inverse_hermitian
      c303_source_comparison_positive) f
#print axioms k303_comparison_operator_nonneg

theorem k303_comparison_lift_nonneg (f : Core (Fin 9) ℂ) :
    0 ≤ (ip f (threeBodyLift k303comparisonOperator f)).re :=
  threeBodyLift_nonneg k303comparisonOperator k303_comparison_operator_nonneg f

#print axioms k303_canonical_gram
#print axioms k303_comparison_operator_form
#print axioms k303_comparison_operator_nonneg
#print axioms k303_comparison_lift_nonneg

end TorusLean.BosonFiniteCertificate
