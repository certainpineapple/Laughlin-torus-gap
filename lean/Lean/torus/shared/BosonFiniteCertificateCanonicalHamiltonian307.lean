import torus.shared.BosonFiniteCertificateCanonicalHamiltonianCore
import torus.shared.BosonFiniteCertificateCanonical307
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

theorem k307_source_length_degree : ∀ a : Fin 8,
    (p307basis a).length = 3 ∧ (p307basis a).sum = 7 := by
  intro a
  fin_cases a <;> decide +kernel

theorem k307_actual_H_raw :
    canonicalPairHamiltonianForm 7 k307occ = complexify p307rawHform := by
  ext a b
  have h := planarHForm_eq_canonicalPair_forms 7 (p307basis a) (p307basis b)
    (k307_source_labels_bounded a) (k307_source_labels_bounded b) (by decide)
    (k307_source_length_degree a).1 (k307_source_length_degree b).1
    (k307_source_length_degree a).2 (k307_source_length_degree b).2
  have ha : scaledWord pairFactorialRoot9 ((p307basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k307occ a) := k307_canonical_source_word a
  have hb : scaledWord pairFactorialRoot9 ((p307basis b).map fin9) =
      canonicalMonomial (factorialScale 8) (k307occ b) := k307_canonical_source_word b
  rw [ha, hb] at h
  exact h.symm

def k307fullFamily : Fin 8 → ThreeSector (Fin 9) :=
  fun a => canonicalThreeMonomial (factorialScale 8) (k307occ a) (k307_particle_degree a)

def k307fullGram : Matrix (Fin 8) (Fin 8) ℚ :=
  Matrix.diagonal (fun a => (k307metric a : ℚ))

theorem k307_full_gram : familyGram k307fullFamily = complexify k307fullGram := by
  calc
    familyGram k307fullFamily = Matrix.diagonal
        (fun a => (occupationMetricWeight (factorialScale 8) (k307occ a) : ℂ)) :=
      canonicalMonomialFamily_gram k307occ k307_occupation_injective k307_particle_degree
    _ = Matrix.diagonal (fun a => (k307metric a : ℂ)) :=
      congrArg Matrix.diagonal k307_metric_complex
    _ = complexify k307fullGram := by
      simp only [k307fullGram, complexify_diagonal_rat, Rat.cast_natCast]

theorem k307_full_inverse_left : p307Ginv * k307fullGram = 1 := by decide +kernel
theorem k307_full_inverse_right : k307fullGram * p307Ginv = 1 := by decide +kernel

theorem k307_full_inverse_complex_left : complexify p307Ginv * complexify k307fullGram = 1 := by
  rw [← complexify_mul_rect, k307_full_inverse_left, complexify_one_rat]
theorem k307_full_inverse_complex_right : complexify k307fullGram * complexify p307Ginv = 1 := by
  rw [← complexify_mul_rect, k307_full_inverse_right, complexify_one_rat]

/-- Riesz compression of the actual pair-removal form to the complete stated
finite occupation block, extended by zero. No torus Hamiltonian identity. -/
def k307pairHamiltonianCompression : ThreeSector (Fin 9) →ₗ[ℂ] ThreeSector (Fin 9) :=
  rankOneRealization k307fullFamily (inverseGramCoefficient (complexify p307Ginv)
    (canonicalPairHamiltonianForm 7 k307occ))

theorem k307_pair_compression_form (x y : Fin 8 → ℂ) :
    ip (familySynthesis k307fullFamily x).val
      (k307pairHamiltonianCompression (familySynthesis k307fullFamily y)).val =
      star x ⬝ᵥ (canonicalPairHamiltonianForm 7 k307occ *ᵥ y) := by
  unfold k307pairHamiltonianCompression
  exact inverseGramRealization_form k307fullFamily (complexify k307fullGram)
    (complexify p307Ginv) (canonicalPairHamiltonianForm 7 k307occ) k307_full_gram
    k307_full_inverse_complex_right k307_full_inverse_complex_left x y

theorem k307_pair_compression_square_form (x y : Fin 8 → ℂ) :
    ip (familySynthesis k307fullFamily x).val
      (k307pairHamiltonianCompression
        (k307pairHamiltonianCompression (familySynthesis k307fullFamily y))).val =
      star x ⬝ᵥ ((canonicalPairHamiltonianForm 7 k307occ * complexify p307Ginv *
        canonicalPairHamiltonianForm 7 k307occ) *ᵥ y) := by
  unfold k307pairHamiltonianCompression
  exact inverseGramRealization_square_form k307fullFamily (complexify k307fullGram)
    (complexify p307Ginv) (canonicalPairHamiltonianForm 7 k307occ) k307_full_gram
    k307_full_inverse_complex_right k307_full_inverse_complex_left x y

#print axioms k307_actual_H_raw
#print axioms k307_full_gram
#print axioms k307_full_inverse_left
#print axioms k307_full_inverse_right
#print axioms k307_pair_compression_form
#print axioms k307_pair_compression_square_form
end TorusLean.BosonFiniteCertificate
