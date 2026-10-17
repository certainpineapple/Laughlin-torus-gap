import torus.shared.BosonFiniteCertificateCanonicalHamiltonianCore
import torus.shared.BosonFiniteCertificateCanonical303
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix
open scoped BigOperators ComplexConjugate
open TorusLean.M2
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonThreeBodyLift
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonFiniteCertificateRealization
open TorusLean.Shared.BosonFiniteCertificateConjugation

theorem k303_source_length_degree : ∀ a : Fin 3,
    (p303basis a).length = 3 ∧ (p303basis a).sum = 3 := by
  intro a
  fin_cases a <;> decide +kernel

theorem k303_actual_H_raw :
    canonicalPairHamiltonianForm 3 k303occ = complexify p303rawHform := by
  ext a b
  have h := planarHForm_eq_canonicalPair_forms 3 (p303basis a) (p303basis b)
    (k303_source_labels_bounded a) (k303_source_labels_bounded b) (by decide)
    (k303_source_length_degree a).1 (k303_source_length_degree b).1
    (k303_source_length_degree a).2 (k303_source_length_degree b).2
  have ha : scaledWord pairFactorialRoot9 ((p303basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k303occ a) := k303_canonical_source_word a
  have hb : scaledWord pairFactorialRoot9 ((p303basis b).map fin9) =
      canonicalMonomial (factorialScale 8) (k303occ b) := k303_canonical_source_word b
  rw [ha, hb] at h
  exact h.symm

def k303fullFamily : Fin 3 → ThreeSector (Fin 9) :=
  fun a => canonicalThreeMonomial (factorialScale 8) (k303occ a) (k303_particle_degree a)

def k303fullGram : Matrix (Fin 3) (Fin 3) ℚ :=
  Matrix.diagonal (fun a => (k303metric a : ℚ))

theorem k303_full_gram : familyGram k303fullFamily = complexify k303fullGram := by
  calc
    familyGram k303fullFamily = Matrix.diagonal
        (fun a => (occupationMetricWeight (factorialScale 8) (k303occ a) : ℂ)) :=
      canonicalMonomialFamily_gram k303occ k303_occupation_injective k303_particle_degree
    _ = Matrix.diagonal (fun a => (k303metric a : ℂ)) :=
      congrArg Matrix.diagonal k303_metric_complex
    _ = complexify k303fullGram := by
      simp only [k303fullGram, complexify_diagonal_rat, Rat.cast_natCast]

theorem k303_full_inverse_left : p303Ginv * k303fullGram = 1 := by decide +kernel
theorem k303_full_inverse_right : k303fullGram * p303Ginv = 1 := by decide +kernel

theorem k303_full_inverse_complex_left : complexify p303Ginv * complexify k303fullGram = 1 := by
  rw [← complexify_mul_rect, k303_full_inverse_left, complexify_one_rat]
theorem k303_full_inverse_complex_right : complexify k303fullGram * complexify p303Ginv = 1 := by
  rw [← complexify_mul_rect, k303_full_inverse_right, complexify_one_rat]

/-- Riesz compression of the actual pair-removal form to the complete stated
finite occupation block, extended by zero. No torus Hamiltonian identity. -/
def k303pairHamiltonianCompression : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k303fullFamily (inverseGramCoefficient (complexify p303Ginv)
    (canonicalPairHamiltonianForm 3 k303occ))

theorem k303_pair_compression_form (x y : Fin 3 → ℂ) :
    ip (familySynthesis k303fullFamily x).val
      (k303pairHamiltonianCompression (familySynthesis k303fullFamily y)).val =
      star x ⬝ᵥ (canonicalPairHamiltonianForm 3 k303occ *ᵥ y) := by
  unfold k303pairHamiltonianCompression
  exact inverseGramRealization_form k303fullFamily (complexify k303fullGram)
    (complexify p303Ginv) (canonicalPairHamiltonianForm 3 k303occ) k303_full_gram
    k303_full_inverse_complex_right k303_full_inverse_complex_left x y

theorem k303_pair_compression_square_form (x y : Fin 3 → ℂ) :
    ip (familySynthesis k303fullFamily x).val
      (k303pairHamiltonianCompression
        (k303pairHamiltonianCompression (familySynthesis k303fullFamily y))).val =
      star x ⬝ᵥ ((canonicalPairHamiltonianForm 3 k303occ * complexify p303Ginv *
        canonicalPairHamiltonianForm 3 k303occ) *ᵥ y) := by
  unfold k303pairHamiltonianCompression
  exact inverseGramRealization_square_form k303fullFamily (complexify k303fullGram)
    (complexify p303Ginv) (canonicalPairHamiltonianForm 3 k303occ) k303_full_gram
    k303_full_inverse_complex_right k303_full_inverse_complex_left x y

#print axioms k303_actual_H_raw
#print axioms k303_full_gram
#print axioms k303_full_inverse_left
#print axioms k303_full_inverse_right
#print axioms k303_pair_compression_form
#print axioms k303_pair_compression_square_form
end TorusLean.BosonFiniteCertificate
