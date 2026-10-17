import torus.shared.BosonFiniteCertificateCanonicalHamiltonianCore
import torus.shared.BosonFiniteCertificateCanonical305
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

theorem k305_source_length_degree : ∀ a : Fin 5,
    (p305basis a).length = 3 ∧ (p305basis a).sum = 5 := by
  intro a
  fin_cases a <;> decide +kernel

theorem k305_actual_H_raw :
    canonicalPairHamiltonianForm 5 k305occ = complexify p305rawHform := by
  ext a b
  have h := planarHForm_eq_canonicalPair_forms 5 (p305basis a) (p305basis b)
    (k305_source_labels_bounded a) (k305_source_labels_bounded b) (by decide)
    (k305_source_length_degree a).1 (k305_source_length_degree b).1
    (k305_source_length_degree a).2 (k305_source_length_degree b).2
  have ha : scaledWord pairFactorialRoot9 ((p305basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k305occ a) := k305_canonical_source_word a
  have hb : scaledWord pairFactorialRoot9 ((p305basis b).map fin9) =
      canonicalMonomial (factorialScale 8) (k305occ b) := k305_canonical_source_word b
  rw [ha, hb] at h
  exact h.symm

def k305fullFamily : Fin 5 → ThreeSector (Fin 9) :=
  fun a => canonicalThreeMonomial (factorialScale 8) (k305occ a) (k305_particle_degree a)

def k305fullGram : Matrix (Fin 5) (Fin 5) ℚ :=
  Matrix.diagonal (fun a => (k305metric a : ℚ))

theorem k305_full_gram : familyGram k305fullFamily = complexify k305fullGram := by
  calc
    familyGram k305fullFamily = Matrix.diagonal
        (fun a => (occupationMetricWeight (factorialScale 8) (k305occ a) : ℂ)) :=
      canonicalMonomialFamily_gram k305occ k305_occupation_injective k305_particle_degree
    _ = Matrix.diagonal (fun a => (k305metric a : ℂ)) :=
      congrArg Matrix.diagonal k305_metric_complex
    _ = complexify k305fullGram := by
      simp only [k305fullGram, complexify_diagonal_rat, Rat.cast_natCast]

theorem k305_full_inverse_left : p305Ginv * k305fullGram = 1 := by decide +kernel
theorem k305_full_inverse_right : k305fullGram * p305Ginv = 1 := by decide +kernel

theorem k305_full_inverse_complex_left : complexify p305Ginv * complexify k305fullGram = 1 := by
  rw [← complexify_mul_rect, k305_full_inverse_left, complexify_one_rat]
theorem k305_full_inverse_complex_right : complexify k305fullGram * complexify p305Ginv = 1 := by
  rw [← complexify_mul_rect, k305_full_inverse_right, complexify_one_rat]

/-- Riesz compression of the actual pair-removal form to the complete stated
finite occupation block, extended by zero. No torus Hamiltonian identity. -/
def k305pairHamiltonianCompression : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k305fullFamily (inverseGramCoefficient (complexify p305Ginv)
    (canonicalPairHamiltonianForm 5 k305occ))

theorem k305_pair_compression_form (x y : Fin 5 → ℂ) :
    ip (familySynthesis k305fullFamily x).val
      (k305pairHamiltonianCompression (familySynthesis k305fullFamily y)).val =
      star x ⬝ᵥ (canonicalPairHamiltonianForm 5 k305occ *ᵥ y) := by
  unfold k305pairHamiltonianCompression
  exact inverseGramRealization_form k305fullFamily (complexify k305fullGram)
    (complexify p305Ginv) (canonicalPairHamiltonianForm 5 k305occ) k305_full_gram
    k305_full_inverse_complex_right k305_full_inverse_complex_left x y

theorem k305_pair_compression_square_form (x y : Fin 5 → ℂ) :
    ip (familySynthesis k305fullFamily x).val
      (k305pairHamiltonianCompression
        (k305pairHamiltonianCompression (familySynthesis k305fullFamily y))).val =
      star x ⬝ᵥ ((canonicalPairHamiltonianForm 5 k305occ * complexify p305Ginv *
        canonicalPairHamiltonianForm 5 k305occ) *ᵥ y) := by
  unfold k305pairHamiltonianCompression
  exact inverseGramRealization_square_form k305fullFamily (complexify k305fullGram)
    (complexify p305Ginv) (canonicalPairHamiltonianForm 5 k305occ) k305_full_gram
    k305_full_inverse_complex_right k305_full_inverse_complex_left x y

#print axioms k305_actual_H_raw
#print axioms k305_full_gram
#print axioms k305_full_inverse_left
#print axioms k305_full_inverse_right
#print axioms k305_pair_compression_form
#print axioms k305_pair_compression_square_form
end TorusLean.BosonFiniteCertificate
