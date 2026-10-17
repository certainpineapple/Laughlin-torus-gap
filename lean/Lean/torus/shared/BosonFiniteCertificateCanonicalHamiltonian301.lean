import torus.shared.BosonFiniteCertificateCanonicalHamiltonianCore
import torus.shared.BosonFiniteCertificateCanonical301
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

theorem k301_source_length_degree : ∀ a : Fin 1,
    (p301basis a).length = 3 ∧ (p301basis a).sum = 1 := by
  intro a
  fin_cases a <;> decide +kernel

theorem k301_actual_H_raw :
    canonicalPairHamiltonianForm 1 k301occ = complexify p301rawHform := by
  ext a b
  have h := planarHForm_eq_canonicalPair_forms 1 (p301basis a) (p301basis b)
    (k301_source_labels_bounded a) (k301_source_labels_bounded b) (by decide)
    (k301_source_length_degree a).1 (k301_source_length_degree b).1
    (k301_source_length_degree a).2 (k301_source_length_degree b).2
  have ha : scaledWord pairFactorialRoot9 ((p301basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k301occ a) := k301_canonical_source_word a
  have hb : scaledWord pairFactorialRoot9 ((p301basis b).map fin9) =
      canonicalMonomial (factorialScale 8) (k301occ b) := k301_canonical_source_word b
  rw [ha, hb] at h
  exact h.symm

def k301fullFamily : Fin 1 → ThreeSector (Fin 9) :=
  fun a => canonicalThreeMonomial (factorialScale 8) (k301occ a) (k301_particle_degree a)

def k301fullGram : Matrix (Fin 1) (Fin 1) ℚ :=
  Matrix.diagonal (fun a => (k301metric a : ℚ))

theorem k301_full_gram : familyGram k301fullFamily = complexify k301fullGram := by
  calc
    familyGram k301fullFamily = Matrix.diagonal
        (fun a => (occupationMetricWeight (factorialScale 8) (k301occ a) : ℂ)) :=
      canonicalMonomialFamily_gram k301occ k301_occupation_injective k301_particle_degree
    _ = Matrix.diagonal (fun a => (k301metric a : ℂ)) :=
      congrArg Matrix.diagonal k301_metric_complex
    _ = complexify k301fullGram := by
      simp only [k301fullGram, complexify_diagonal_rat, Rat.cast_natCast]

theorem k301_full_inverse_left : p301Ginv * k301fullGram = 1 := by decide +kernel
theorem k301_full_inverse_right : k301fullGram * p301Ginv = 1 := by decide +kernel

theorem k301_full_inverse_complex_left : complexify p301Ginv * complexify k301fullGram = 1 := by
  rw [← complexify_mul_rect, k301_full_inverse_left, complexify_one_rat]
theorem k301_full_inverse_complex_right : complexify k301fullGram * complexify p301Ginv = 1 := by
  rw [← complexify_mul_rect, k301_full_inverse_right, complexify_one_rat]

/-- Riesz compression of the actual pair-removal form to the complete stated
finite occupation block, extended by zero. No torus Hamiltonian identity. -/
def k301pairHamiltonianCompression : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k301fullFamily (inverseGramCoefficient (complexify p301Ginv)
    (canonicalPairHamiltonianForm 1 k301occ))

theorem k301_pair_compression_form (x y : Fin 1 → ℂ) :
    ip (familySynthesis k301fullFamily x).val
      (k301pairHamiltonianCompression (familySynthesis k301fullFamily y)).val =
      star x ⬝ᵥ (canonicalPairHamiltonianForm 1 k301occ *ᵥ y) := by
  unfold k301pairHamiltonianCompression
  exact inverseGramRealization_form k301fullFamily (complexify k301fullGram)
    (complexify p301Ginv) (canonicalPairHamiltonianForm 1 k301occ) k301_full_gram
    k301_full_inverse_complex_right k301_full_inverse_complex_left x y

theorem k301_pair_compression_square_form (x y : Fin 1 → ℂ) :
    ip (familySynthesis k301fullFamily x).val
      (k301pairHamiltonianCompression
        (k301pairHamiltonianCompression (familySynthesis k301fullFamily y))).val =
      star x ⬝ᵥ ((canonicalPairHamiltonianForm 1 k301occ * complexify p301Ginv *
        canonicalPairHamiltonianForm 1 k301occ) *ᵥ y) := by
  unfold k301pairHamiltonianCompression
  exact inverseGramRealization_square_form k301fullFamily (complexify k301fullGram)
    (complexify p301Ginv) (canonicalPairHamiltonianForm 1 k301occ) k301_full_gram
    k301_full_inverse_complex_right k301_full_inverse_complex_left x y

#print axioms k301_actual_H_raw
#print axioms k301_full_gram
#print axioms k301_full_inverse_left
#print axioms k301_full_inverse_right
#print axioms k301_pair_compression_form
#print axioms k301_pair_compression_square_form
end TorusLean.BosonFiniteCertificate
