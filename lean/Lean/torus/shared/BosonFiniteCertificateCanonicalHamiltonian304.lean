import torus.shared.BosonFiniteCertificateCanonicalHamiltonianCore
import torus.shared.BosonFiniteCertificateCanonical304
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

theorem k304_source_length_degree : ∀ a : Fin 4,
    (p304basis a).length = 3 ∧ (p304basis a).sum = 4 := by
  intro a
  fin_cases a <;> decide +kernel

theorem k304_actual_H_raw :
    canonicalPairHamiltonianForm 4 k304occ = complexify p304rawHform := by
  ext a b
  have h := planarHForm_eq_canonicalPair_forms 4 (p304basis a) (p304basis b)
    (k304_source_labels_bounded a) (k304_source_labels_bounded b) (by decide)
    (k304_source_length_degree a).1 (k304_source_length_degree b).1
    (k304_source_length_degree a).2 (k304_source_length_degree b).2
  have ha : scaledWord pairFactorialRoot9 ((p304basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k304occ a) := k304_canonical_source_word a
  have hb : scaledWord pairFactorialRoot9 ((p304basis b).map fin9) =
      canonicalMonomial (factorialScale 8) (k304occ b) := k304_canonical_source_word b
  rw [ha, hb] at h
  exact h.symm

def k304fullFamily : Fin 4 → ThreeSector (Fin 9) :=
  fun a => canonicalThreeMonomial (factorialScale 8) (k304occ a) (k304_particle_degree a)

def k304fullGram : Matrix (Fin 4) (Fin 4) ℚ :=
  Matrix.diagonal (fun a => (k304metric a : ℚ))

theorem k304_full_gram : familyGram k304fullFamily = complexify k304fullGram := by
  calc
    familyGram k304fullFamily = Matrix.diagonal
        (fun a => (occupationMetricWeight (factorialScale 8) (k304occ a) : ℂ)) :=
      canonicalMonomialFamily_gram k304occ k304_occupation_injective k304_particle_degree
    _ = Matrix.diagonal (fun a => (k304metric a : ℂ)) :=
      congrArg Matrix.diagonal k304_metric_complex
    _ = complexify k304fullGram := by
      simp only [k304fullGram, complexify_diagonal_rat, Rat.cast_natCast]

theorem k304_full_inverse_left : p304Ginv * k304fullGram = 1 := by decide +kernel
theorem k304_full_inverse_right : k304fullGram * p304Ginv = 1 := by decide +kernel

theorem k304_full_inverse_complex_left : complexify p304Ginv * complexify k304fullGram = 1 := by
  rw [← complexify_mul_rect, k304_full_inverse_left, complexify_one_rat]
theorem k304_full_inverse_complex_right : complexify k304fullGram * complexify p304Ginv = 1 := by
  rw [← complexify_mul_rect, k304_full_inverse_right, complexify_one_rat]

/-- Riesz compression of the actual pair-removal form to the complete stated
finite occupation block, extended by zero. No torus Hamiltonian identity. -/
def k304pairHamiltonianCompression : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k304fullFamily (inverseGramCoefficient (complexify p304Ginv)
    (canonicalPairHamiltonianForm 4 k304occ))

theorem k304_pair_compression_form (x y : Fin 4 → ℂ) :
    ip (familySynthesis k304fullFamily x).val
      (k304pairHamiltonianCompression (familySynthesis k304fullFamily y)).val =
      star x ⬝ᵥ (canonicalPairHamiltonianForm 4 k304occ *ᵥ y) := by
  unfold k304pairHamiltonianCompression
  exact inverseGramRealization_form k304fullFamily (complexify k304fullGram)
    (complexify p304Ginv) (canonicalPairHamiltonianForm 4 k304occ) k304_full_gram
    k304_full_inverse_complex_right k304_full_inverse_complex_left x y

theorem k304_pair_compression_square_form (x y : Fin 4 → ℂ) :
    ip (familySynthesis k304fullFamily x).val
      (k304pairHamiltonianCompression
        (k304pairHamiltonianCompression (familySynthesis k304fullFamily y))).val =
      star x ⬝ᵥ ((canonicalPairHamiltonianForm 4 k304occ * complexify p304Ginv *
        canonicalPairHamiltonianForm 4 k304occ) *ᵥ y) := by
  unfold k304pairHamiltonianCompression
  exact inverseGramRealization_square_form k304fullFamily (complexify k304fullGram)
    (complexify p304Ginv) (canonicalPairHamiltonianForm 4 k304occ) k304_full_gram
    k304_full_inverse_complex_right k304_full_inverse_complex_left x y

#print axioms k304_actual_H_raw
#print axioms k304_full_gram
#print axioms k304_full_inverse_left
#print axioms k304_full_inverse_right
#print axioms k304_pair_compression_form
#print axioms k304_pair_compression_square_form
end TorusLean.BosonFiniteCertificate
