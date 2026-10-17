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

theorem k301_family_complex : k301family =
    (fun j => canonicalThreeBlock (factorialScale 8) k301occ k301_particle_degree
      (fun a => complexify b301relative a j)) := by
  rfl
#print axioms k301_family_complex

theorem k301_metric_complex :
    (fun a => (occupationMetricWeight (factorialScale 8) (k301occ a) : ℂ)) =
      (fun a => (k301metric a : ℂ)) := by
  funext a
  exact congrArg (fun q : ℕ => (q : ℂ)) (congrFun k301_metric_reconstructed a)
#print axioms k301_metric_complex

theorem k301_gram_complex_reconstructed : (complexify b301relative)ᴴ *
    Matrix.diagonal (fun a => (k301metric a : ℂ)) * complexify b301relative =
    complexify k301F := by
  have he := congrArg (fun A => complexify A) k301_gram_reconstructed
  simpa only [complexify_mul_rect, complexify_transpose_rect, complexify_diagonal_rat,
    Rat.cast_natCast] using he
#print axioms k301_gram_complex_reconstructed

theorem k301_canonical_gram : familyGram k301family = complexify k301F := by
  calc
    familyGram k301family = familyGram (fun j =>
        canonicalThreeBlock (factorialScale 8) k301occ k301_particle_degree
          (fun a => complexify b301relative a j)) :=
      congrArg familyGram k301_family_complex
    _ = (complexify b301relative)ᴴ * Matrix.diagonal
        (fun a => (occupationMetricWeight (factorialScale 8) (k301occ a) : ℂ)) *
        complexify b301relative :=
      canonicalRelativeFamily_gram (factorialScale 8) k301occ
        k301_occupation_injective k301_particle_degree (complexify b301relative)
    _ = (complexify b301relative)ᴴ * Matrix.diagonal
        (fun a => (k301metric a : ℂ)) * complexify b301relative := by
      rw [k301_metric_complex]
    _ = complexify k301F := k301_gram_complex_reconstructed
#print axioms k301_canonical_gram

theorem k301_inverse_complex_left : complexify k301J * complexify k301F = 1 := by
  rw [← complexify_mul_rect, k301_inverse_left, complexify_one_rat]

theorem k301_inverse_complex_right : complexify k301F * complexify k301J = 1 := by
  rw [← complexify_mul_rect, k301_inverse_right, complexify_one_rat]

theorem k301_inverse_hermitian : (complexify k301J).IsHermitian := by
  rw [Matrix.IsHermitian, ← complexify_transpose_rect, k301_inverse_symmetric]

/-- The concrete Riesz operator of the original-row planar E3 comparison in
its finite relative coordinate block, represented in the canonical N=3 carrier. -/
def k301comparisonOperator : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k301family
    (inverseGramCoefficient (complexify k301J) (complexify c301comparisonRaw))

theorem k301_comparison_operator_form (x y : Fin 0 → ℂ) :
    ip (familySynthesis k301family x).val
      (k301comparisonOperator (familySynthesis k301family y)).val =
      star x ⬝ᵥ (complexify c301comparisonRaw *ᵥ y) := by
  unfold k301comparisonOperator
  exact inverseGramRealization_form k301family (complexify k301F) (complexify k301J)
    (complexify c301comparisonRaw) k301_canonical_gram
    k301_inverse_complex_right k301_inverse_complex_left x y
#print axioms k301_comparison_operator_form

theorem k301_comparison_operator_nonneg (f : ThreeSector (Fin 9)) :
    0 ≤ (ip f.val (k301comparisonOperator f).val).re := by
  unfold k301comparisonOperator
  exact rankOneRealization_nonneg k301family
    (inverseGramCoefficient (complexify k301J) (complexify c301comparisonRaw))
    (inverseGramCoefficient_posSemidef (complexify k301J) (complexify c301comparisonRaw)
      k301_inverse_hermitian
      c301_source_comparison_positive) f
#print axioms k301_comparison_operator_nonneg

theorem k301_comparison_lift_nonneg (f : Core (Fin 9) ℂ) :
    0 ≤ (ip f (threeBodyLift k301comparisonOperator f)).re :=
  threeBodyLift_nonneg k301comparisonOperator k301_comparison_operator_nonneg f

#print axioms k301_canonical_gram
#print axioms k301_comparison_operator_form
#print axioms k301_comparison_operator_nonneg
#print axioms k301_comparison_lift_nonneg

end TorusLean.BosonFiniteCertificate
