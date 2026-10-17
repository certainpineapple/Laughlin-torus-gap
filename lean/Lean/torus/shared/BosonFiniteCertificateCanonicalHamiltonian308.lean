import torus.shared.BosonFiniteCertificateCanonicalHamiltonianCore
import torus.shared.BosonFiniteCertificateCanonical308
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

theorem k308_source_length_degree : ∀ a : Fin 10,
    (p308basis a).length = 3 ∧ (p308basis a).sum = 8 := by
  intro a
  fin_cases a <;> decide +kernel

theorem k308_actual_H_raw :
    canonicalPairHamiltonianForm 8 k308occ = complexify p308rawHform := by
  ext a b
  have h := planarHForm_eq_canonicalPair_forms 8 (p308basis a) (p308basis b)
    (k308_source_labels_bounded a) (k308_source_labels_bounded b) (by decide)
    (k308_source_length_degree a).1 (k308_source_length_degree b).1
    (k308_source_length_degree a).2 (k308_source_length_degree b).2
  have ha : scaledWord pairFactorialRoot9 ((p308basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k308occ a) := k308_canonical_source_word a
  have hb : scaledWord pairFactorialRoot9 ((p308basis b).map fin9) =
      canonicalMonomial (factorialScale 8) (k308occ b) := k308_canonical_source_word b
  rw [ha, hb] at h
  exact h.symm

def k308fullFamily : Fin 10 → ThreeSector (Fin 9) :=
  fun a => canonicalThreeMonomial (factorialScale 8) (k308occ a) (k308_particle_degree a)

def k308fullGram : Matrix (Fin 10) (Fin 10) ℚ :=
  Matrix.diagonal (fun a => (k308metric a : ℚ))

theorem k308_full_gram : familyGram k308fullFamily = complexify k308fullGram := by
  calc
    familyGram k308fullFamily = Matrix.diagonal
        (fun a => (occupationMetricWeight (factorialScale 8) (k308occ a) : ℂ)) :=
      canonicalMonomialFamily_gram k308occ k308_occupation_injective k308_particle_degree
    _ = Matrix.diagonal (fun a => (k308metric a : ℂ)) :=
      congrArg Matrix.diagonal k308_metric_complex
    _ = complexify k308fullGram := by
      simp only [k308fullGram, complexify_diagonal_rat, Rat.cast_natCast]

theorem k308_full_inverse_left : p308Ginv * k308fullGram = 1 := by decide +kernel
theorem k308_full_inverse_right : k308fullGram * p308Ginv = 1 := by decide +kernel

theorem k308_full_inverse_complex_left : complexify p308Ginv * complexify k308fullGram = 1 := by
  rw [← complexify_mul_rect, k308_full_inverse_left, complexify_one_rat]
theorem k308_full_inverse_complex_right : complexify k308fullGram * complexify p308Ginv = 1 := by
  rw [← complexify_mul_rect, k308_full_inverse_right, complexify_one_rat]

/-- Riesz compression of the actual pair-removal form to the complete stated
finite occupation block, extended by zero. No torus Hamiltonian identity. -/
def k308pairHamiltonianCompression : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k308fullFamily (inverseGramCoefficient (complexify p308Ginv)
    (canonicalPairHamiltonianForm 8 k308occ))

theorem k308_pair_compression_form (x y : Fin 10 → ℂ) :
    ip (familySynthesis k308fullFamily x).val
      (k308pairHamiltonianCompression (familySynthesis k308fullFamily y)).val =
      star x ⬝ᵥ (canonicalPairHamiltonianForm 8 k308occ *ᵥ y) := by
  unfold k308pairHamiltonianCompression
  exact inverseGramRealization_form k308fullFamily (complexify k308fullGram)
    (complexify p308Ginv) (canonicalPairHamiltonianForm 8 k308occ) k308_full_gram
    k308_full_inverse_complex_right k308_full_inverse_complex_left x y

theorem k308_pair_compression_square_form (x y : Fin 10 → ℂ) :
    ip (familySynthesis k308fullFamily x).val
      (k308pairHamiltonianCompression
        (k308pairHamiltonianCompression (familySynthesis k308fullFamily y))).val =
      star x ⬝ᵥ ((canonicalPairHamiltonianForm 8 k308occ * complexify p308Ginv *
        canonicalPairHamiltonianForm 8 k308occ) *ᵥ y) := by
  unfold k308pairHamiltonianCompression
  exact inverseGramRealization_square_form k308fullFamily (complexify k308fullGram)
    (complexify p308Ginv) (canonicalPairHamiltonianForm 8 k308occ) k308_full_gram
    k308_full_inverse_complex_right k308_full_inverse_complex_left x y

#print axioms k308_actual_H_raw
#print axioms k308_full_gram
#print axioms k308_full_inverse_left
#print axioms k308_full_inverse_right
#print axioms k308_pair_compression_form
#print axioms k308_pair_compression_square_form
end TorusLean.BosonFiniteCertificate
