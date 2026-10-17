import torus.shared.BosonFiniteCertificateCanonicalHamiltonianCore
import torus.shared.BosonFiniteCertificateCanonical306
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

theorem k306_source_length_degree : ∀ a : Fin 7,
    (p306basis a).length = 3 ∧ (p306basis a).sum = 6 := by
  intro a
  fin_cases a <;> decide +kernel

theorem k306_actual_H_raw :
    canonicalPairHamiltonianForm 6 k306occ = complexify p306rawHform := by
  ext a b
  have h := planarHForm_eq_canonicalPair_forms 6 (p306basis a) (p306basis b)
    (k306_source_labels_bounded a) (k306_source_labels_bounded b) (by decide)
    (k306_source_length_degree a).1 (k306_source_length_degree b).1
    (k306_source_length_degree a).2 (k306_source_length_degree b).2
  have ha : scaledWord pairFactorialRoot9 ((p306basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k306occ a) := k306_canonical_source_word a
  have hb : scaledWord pairFactorialRoot9 ((p306basis b).map fin9) =
      canonicalMonomial (factorialScale 8) (k306occ b) := k306_canonical_source_word b
  rw [ha, hb] at h
  exact h.symm

def k306fullFamily : Fin 7 → ThreeSector (Fin 9) :=
  fun a => canonicalThreeMonomial (factorialScale 8) (k306occ a) (k306_particle_degree a)

def k306fullGram : Matrix (Fin 7) (Fin 7) ℚ :=
  Matrix.diagonal (fun a => (k306metric a : ℚ))

theorem k306_full_gram : familyGram k306fullFamily = complexify k306fullGram := by
  calc
    familyGram k306fullFamily = Matrix.diagonal
        (fun a => (occupationMetricWeight (factorialScale 8) (k306occ a) : ℂ)) :=
      canonicalMonomialFamily_gram k306occ k306_occupation_injective k306_particle_degree
    _ = Matrix.diagonal (fun a => (k306metric a : ℂ)) :=
      congrArg Matrix.diagonal k306_metric_complex
    _ = complexify k306fullGram := by
      simp only [k306fullGram, complexify_diagonal_rat, Rat.cast_natCast]

theorem k306_full_inverse_left : p306Ginv * k306fullGram = 1 := by decide +kernel
theorem k306_full_inverse_right : k306fullGram * p306Ginv = 1 := by decide +kernel

theorem k306_full_inverse_complex_left : complexify p306Ginv * complexify k306fullGram = 1 := by
  rw [← complexify_mul_rect, k306_full_inverse_left, complexify_one_rat]
theorem k306_full_inverse_complex_right : complexify k306fullGram * complexify p306Ginv = 1 := by
  rw [← complexify_mul_rect, k306_full_inverse_right, complexify_one_rat]

/-- Riesz compression of the actual pair-removal form to the complete stated
finite occupation block, extended by zero. No torus Hamiltonian identity. -/
def k306pairHamiltonianCompression : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k306fullFamily (inverseGramCoefficient (complexify p306Ginv)
    (canonicalPairHamiltonianForm 6 k306occ))

theorem k306_pair_compression_form (x y : Fin 7 → ℂ) :
    ip (familySynthesis k306fullFamily x).val
      (k306pairHamiltonianCompression (familySynthesis k306fullFamily y)).val =
      star x ⬝ᵥ (canonicalPairHamiltonianForm 6 k306occ *ᵥ y) := by
  unfold k306pairHamiltonianCompression
  exact inverseGramRealization_form k306fullFamily (complexify k306fullGram)
    (complexify p306Ginv) (canonicalPairHamiltonianForm 6 k306occ) k306_full_gram
    k306_full_inverse_complex_right k306_full_inverse_complex_left x y

theorem k306_pair_compression_square_form (x y : Fin 7 → ℂ) :
    ip (familySynthesis k306fullFamily x).val
      (k306pairHamiltonianCompression
        (k306pairHamiltonianCompression (familySynthesis k306fullFamily y))).val =
      star x ⬝ᵥ ((canonicalPairHamiltonianForm 6 k306occ * complexify p306Ginv *
        canonicalPairHamiltonianForm 6 k306occ) *ᵥ y) := by
  unfold k306pairHamiltonianCompression
  exact inverseGramRealization_square_form k306fullFamily (complexify k306fullGram)
    (complexify p306Ginv) (canonicalPairHamiltonianForm 6 k306occ) k306_full_gram
    k306_full_inverse_complex_right k306_full_inverse_complex_left x y

#print axioms k306_actual_H_raw
#print axioms k306_full_gram
#print axioms k306_full_inverse_left
#print axioms k306_full_inverse_right
#print axioms k306_pair_compression_form
#print axioms k306_pair_compression_square_form
end TorusLean.BosonFiniteCertificate
