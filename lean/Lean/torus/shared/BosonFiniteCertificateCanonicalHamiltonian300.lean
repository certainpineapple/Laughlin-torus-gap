import torus.shared.BosonFiniteCertificateCanonicalHamiltonianCore
import torus.shared.BosonFiniteCertificateCanonical300
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

theorem k300_source_length_degree : ∀ a : Fin 1,
    (p300basis a).length = 3 ∧ (p300basis a).sum = 0 := by
  intro a
  fin_cases a <;> decide +kernel

theorem k300_actual_H_raw :
    canonicalPairHamiltonianForm 0 k300occ = complexify p300rawHform := by
  ext a b
  have h := planarHForm_eq_canonicalPair_forms 0 (p300basis a) (p300basis b)
    (k300_source_labels_bounded a) (k300_source_labels_bounded b) (by decide)
    (k300_source_length_degree a).1 (k300_source_length_degree b).1
    (k300_source_length_degree a).2 (k300_source_length_degree b).2
  have ha : scaledWord pairFactorialRoot9 ((p300basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k300occ a) := k300_canonical_source_word a
  have hb : scaledWord pairFactorialRoot9 ((p300basis b).map fin9) =
      canonicalMonomial (factorialScale 8) (k300occ b) := k300_canonical_source_word b
  rw [ha, hb] at h
  exact h.symm

def k300fullFamily : Fin 1 → ThreeSector (Fin 9) :=
  fun a => canonicalThreeMonomial (factorialScale 8) (k300occ a) (k300_particle_degree a)

def k300fullGram : Matrix (Fin 1) (Fin 1) ℚ :=
  Matrix.diagonal (fun a => (k300metric a : ℚ))

theorem k300_full_gram : familyGram k300fullFamily = complexify k300fullGram := by
  calc
    familyGram k300fullFamily = Matrix.diagonal
        (fun a => (occupationMetricWeight (factorialScale 8) (k300occ a) : ℂ)) :=
      canonicalMonomialFamily_gram k300occ k300_occupation_injective k300_particle_degree
    _ = Matrix.diagonal (fun a => (k300metric a : ℂ)) :=
      congrArg Matrix.diagonal k300_metric_complex
    _ = complexify k300fullGram := by
      simp only [k300fullGram, complexify_diagonal_rat, Rat.cast_natCast]

theorem k300_full_inverse_left : p300Ginv * k300fullGram = 1 := by decide +kernel
theorem k300_full_inverse_right : k300fullGram * p300Ginv = 1 := by decide +kernel

theorem k300_full_inverse_complex_left : complexify p300Ginv * complexify k300fullGram = 1 := by
  rw [← complexify_mul_rect, k300_full_inverse_left, complexify_one_rat]
theorem k300_full_inverse_complex_right : complexify k300fullGram * complexify p300Ginv = 1 := by
  rw [← complexify_mul_rect, k300_full_inverse_right, complexify_one_rat]

/-- Riesz compression of the actual pair-removal form to the complete stated
finite occupation block, extended by zero. No torus Hamiltonian identity. -/
def k300pairHamiltonianCompression : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k300fullFamily (inverseGramCoefficient (complexify p300Ginv)
    (canonicalPairHamiltonianForm 0 k300occ))

theorem k300_pair_compression_form (x y : Fin 1 → ℂ) :
    ip (familySynthesis k300fullFamily x).val
      (k300pairHamiltonianCompression (familySynthesis k300fullFamily y)).val =
      star x ⬝ᵥ (canonicalPairHamiltonianForm 0 k300occ *ᵥ y) := by
  unfold k300pairHamiltonianCompression
  exact inverseGramRealization_form k300fullFamily (complexify k300fullGram)
    (complexify p300Ginv) (canonicalPairHamiltonianForm 0 k300occ) k300_full_gram
    k300_full_inverse_complex_right k300_full_inverse_complex_left x y

theorem k300_pair_compression_square_form (x y : Fin 1 → ℂ) :
    ip (familySynthesis k300fullFamily x).val
      (k300pairHamiltonianCompression
        (k300pairHamiltonianCompression (familySynthesis k300fullFamily y))).val =
      star x ⬝ᵥ ((canonicalPairHamiltonianForm 0 k300occ * complexify p300Ginv *
        canonicalPairHamiltonianForm 0 k300occ) *ᵥ y) := by
  unfold k300pairHamiltonianCompression
  exact inverseGramRealization_square_form k300fullFamily (complexify k300fullGram)
    (complexify p300Ginv) (canonicalPairHamiltonianForm 0 k300occ) k300_full_gram
    k300_full_inverse_complex_right k300_full_inverse_complex_left x y

#print axioms k300_actual_H_raw
#print axioms k300_full_gram
#print axioms k300_full_inverse_left
#print axioms k300_full_inverse_right
#print axioms k300_pair_compression_form
#print axioms k300_pair_compression_square_form
end TorusLean.BosonFiniteCertificate
