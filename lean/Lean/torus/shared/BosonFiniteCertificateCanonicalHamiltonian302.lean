import torus.shared.BosonFiniteCertificateCanonicalHamiltonianCore
import torus.shared.BosonFiniteCertificateCanonical302
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

theorem k302_source_length_degree : ∀ a : Fin 2,
    (p302basis a).length = 3 ∧ (p302basis a).sum = 2 := by
  intro a
  fin_cases a <;> decide +kernel

theorem k302_actual_H_raw :
    canonicalPairHamiltonianForm 2 k302occ = complexify p302rawHform := by
  ext a b
  have h := planarHForm_eq_canonicalPair_forms 2 (p302basis a) (p302basis b)
    (k302_source_labels_bounded a) (k302_source_labels_bounded b) (by decide)
    (k302_source_length_degree a).1 (k302_source_length_degree b).1
    (k302_source_length_degree a).2 (k302_source_length_degree b).2
  have ha : scaledWord pairFactorialRoot9 ((p302basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k302occ a) := k302_canonical_source_word a
  have hb : scaledWord pairFactorialRoot9 ((p302basis b).map fin9) =
      canonicalMonomial (factorialScale 8) (k302occ b) := k302_canonical_source_word b
  rw [ha, hb] at h
  exact h.symm

def k302fullFamily : Fin 2 → ThreeSector (Fin 9) :=
  fun a => canonicalThreeMonomial (factorialScale 8) (k302occ a) (k302_particle_degree a)

def k302fullGram : Matrix (Fin 2) (Fin 2) ℚ :=
  Matrix.diagonal (fun a => (k302metric a : ℚ))

theorem k302_full_gram : familyGram k302fullFamily = complexify k302fullGram := by
  calc
    familyGram k302fullFamily = Matrix.diagonal
        (fun a => (occupationMetricWeight (factorialScale 8) (k302occ a) : ℂ)) :=
      canonicalMonomialFamily_gram k302occ k302_occupation_injective k302_particle_degree
    _ = Matrix.diagonal (fun a => (k302metric a : ℂ)) :=
      congrArg Matrix.diagonal k302_metric_complex
    _ = complexify k302fullGram := by
      simp only [k302fullGram, complexify_diagonal_rat, Rat.cast_natCast]

theorem k302_full_inverse_left : p302Ginv * k302fullGram = 1 := by decide +kernel
theorem k302_full_inverse_right : k302fullGram * p302Ginv = 1 := by decide +kernel

theorem k302_full_inverse_complex_left : complexify p302Ginv * complexify k302fullGram = 1 := by
  rw [← complexify_mul_rect, k302_full_inverse_left, complexify_one_rat]
theorem k302_full_inverse_complex_right : complexify k302fullGram * complexify p302Ginv = 1 := by
  rw [← complexify_mul_rect, k302_full_inverse_right, complexify_one_rat]

/-- Riesz compression of the actual pair-removal form to the complete stated
finite occupation block, extended by zero. No torus Hamiltonian identity. -/
def k302pairHamiltonianCompression : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k302fullFamily (inverseGramCoefficient (complexify p302Ginv)
    (canonicalPairHamiltonianForm 2 k302occ))

theorem k302_pair_compression_form (x y : Fin 2 → ℂ) :
    ip (familySynthesis k302fullFamily x).val
      (k302pairHamiltonianCompression (familySynthesis k302fullFamily y)).val =
      star x ⬝ᵥ (canonicalPairHamiltonianForm 2 k302occ *ᵥ y) := by
  unfold k302pairHamiltonianCompression
  exact inverseGramRealization_form k302fullFamily (complexify k302fullGram)
    (complexify p302Ginv) (canonicalPairHamiltonianForm 2 k302occ) k302_full_gram
    k302_full_inverse_complex_right k302_full_inverse_complex_left x y

theorem k302_pair_compression_square_form (x y : Fin 2 → ℂ) :
    ip (familySynthesis k302fullFamily x).val
      (k302pairHamiltonianCompression
        (k302pairHamiltonianCompression (familySynthesis k302fullFamily y))).val =
      star x ⬝ᵥ ((canonicalPairHamiltonianForm 2 k302occ * complexify p302Ginv *
        canonicalPairHamiltonianForm 2 k302occ) *ᵥ y) := by
  unfold k302pairHamiltonianCompression
  exact inverseGramRealization_square_form k302fullFamily (complexify k302fullGram)
    (complexify p302Ginv) (canonicalPairHamiltonianForm 2 k302occ) k302_full_gram
    k302_full_inverse_complex_right k302_full_inverse_complex_left x y

#print axioms k302_actual_H_raw
#print axioms k302_full_gram
#print axioms k302_full_inverse_left
#print axioms k302_full_inverse_right
#print axioms k302_pair_compression_form
#print axioms k302_pair_compression_square_form
end TorusLean.BosonFiniteCertificate
