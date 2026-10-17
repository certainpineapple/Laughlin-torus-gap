import torus.shared.BosonFiniteCertificateCanonicalHamiltonian303
import torus.shared.BosonFiniteCertificateCanonicalPairBlock
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
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.BosonFiniteCertificateCanonicalPairInvariant

theorem k303_actual_pair_block_form :
    actualPairBlockForm 3 k303occ = complexify p303rawHform := by
  have h : actualPairBlockForm 3 k303occ = canonicalPairHamiltonianForm 3 k303occ := by
    ext a b
    exact actualPairBlockForm_pair_forms 3 k303occ a b
  rw [h, k303_actual_H_raw]

theorem k303_inverse_diagonal :
    p303Ginv = Matrix.diagonal (fun a => (k303metric a : ℚ)⁻¹) := by decide +kernel

theorem k303_actual_full_inverse :
    canonicalFullInverseGram k303occ = complexify p303Ginv := by
  rw [k303_inverse_diagonal, complexify_diagonal_rat]
  unfold canonicalFullInverseGram
  apply congrArg Matrix.diagonal
  funext a
  rw [congrFun k303_metric_complex a]
  simp only [Rat.cast_inv, Rat.cast_natCast]

/-- This action is derived from the actual differential H and its true
adjoint creator, after proving that every output remains in the same block. -/
theorem k303_actual_pair_hamiltonian_action (x : Fin 3 → ℂ) :
    canonicalPairHamiltonian9 3 (canonicalBlock (factorialScale 8) k303occ x) =
      canonicalBlock (factorialScale 8) k303occ
        ((complexify p303Ginv * complexify p303rawHform) *ᵥ x) := by
  have h := canonicalPairHamiltonian9_block_action 3 (by decide)
    k303occ k303_occupation_injective p303basis
    (fun a => k303_canonical_source_word a)
    (fun a => (k303_source_length_degree a).1)
    (fun a => (k303_source_length_degree a).2)
    (fun p a => k303_pair_output_membership p a) x
  simpa only [k303_actual_full_inverse, k303_actual_pair_block_form] using h

/-- H applied twice is the original differential operator composed with
itself, justified by its genuine finite-block invariance. -/
theorem k303_actual_pair_hamiltonian_square_form (x y : Fin 3 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k303occ x)
      (canonicalPairHamiltonian9 3
        (canonicalPairHamiltonian9 3 (canonicalBlock (factorialScale 8) k303occ y))) =
      star x ⬝ᵥ ((complexify p303rawHform * complexify p303Ginv *
        complexify p303rawHform) *ᵥ y) := by
  have h := canonicalPairHamiltonian9_block_square 3 (by decide)
    k303occ k303_occupation_injective p303basis
    (fun a => k303_canonical_source_word a)
    (fun a => (k303_source_length_degree a).1)
    (fun a => (k303_source_length_degree a).2)
    (fun p a => k303_pair_output_membership p a) x y
  simpa only [k303_actual_full_inverse, k303_actual_pair_block_form] using h

/-- All nine source degree blocks use one and the same genuine finite H_8.
The extra pair degrees vanish by actual derivative action, not a matrix cutoff. -/
theorem k303_common_pair_hamiltonian (x : Fin 3 → ℂ) :
    canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k303occ x) =
      canonicalPairHamiltonian9 3 (canonicalBlock (factorialScale 8) k303occ x) := by
  simp only [canonicalBlock, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  have ha : scaledWord pairFactorialRoot9 ((p303basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k303occ a) := k303_canonical_source_word a
  simpa only [ha] using canonicalPairHamiltonian9_cutoff_word 3 8 (by decide) (by decide)
    (p303basis a) (k303_source_labels_bounded a)
    (k303_source_length_degree a).1 (k303_source_length_degree a).2

theorem k303_actual_common_pair_hamiltonian_action (x : Fin 3 → ℂ) :
    canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k303occ x) =
      canonicalBlock (factorialScale 8) k303occ
        ((complexify p303Ginv * complexify p303rawHform) *ᵥ x) := by
  rw [k303_common_pair_hamiltonian x, k303_actual_pair_hamiltonian_action x]

theorem k303_actual_common_pair_hamiltonian_form (x y : Fin 3 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k303occ x)
      (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k303occ y)) =
      star x ⬝ᵥ (complexify p303rawHform *ᵥ y) := by
  rw [k303_common_pair_hamiltonian y, actualPairBlock_cross_form, k303_actual_pair_block_form]

theorem k303_actual_common_pair_hamiltonian_square_form (x y : Fin 3 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k303occ x)
      (canonicalPairHamiltonian9 8
        (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k303occ y))) =
      star x ⬝ᵥ ((complexify p303rawHform * complexify p303Ginv *
        complexify p303rawHform) *ᵥ y) := by
  rw [k303_actual_common_pair_hamiltonian_action y,
    k303_actual_common_pair_hamiltonian_form x
      ((complexify p303Ginv * complexify p303rawHform) *ᵥ y)]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

#print axioms k303_common_pair_hamiltonian
#print axioms k303_actual_common_pair_hamiltonian_action
#print axioms k303_actual_common_pair_hamiltonian_form
#print axioms k303_actual_common_pair_hamiltonian_square_form

#print axioms k303_actual_pair_block_form
#print axioms k303_actual_full_inverse
#print axioms k303_actual_pair_hamiltonian_action
#print axioms k303_actual_pair_hamiltonian_square_form
end TorusLean.BosonFiniteCertificate
