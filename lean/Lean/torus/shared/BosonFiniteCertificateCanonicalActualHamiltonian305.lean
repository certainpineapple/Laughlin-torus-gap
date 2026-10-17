import torus.shared.BosonFiniteCertificateCanonicalHamiltonian305
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

theorem k305_actual_pair_block_form :
    actualPairBlockForm 5 k305occ = complexify p305rawHform := by
  have h : actualPairBlockForm 5 k305occ = canonicalPairHamiltonianForm 5 k305occ := by
    ext a b
    exact actualPairBlockForm_pair_forms 5 k305occ a b
  rw [h, k305_actual_H_raw]

theorem k305_inverse_diagonal :
    p305Ginv = Matrix.diagonal (fun a => (k305metric a : ℚ)⁻¹) := by decide +kernel

theorem k305_actual_full_inverse :
    canonicalFullInverseGram k305occ = complexify p305Ginv := by
  rw [k305_inverse_diagonal, complexify_diagonal_rat]
  unfold canonicalFullInverseGram
  apply congrArg Matrix.diagonal
  funext a
  rw [congrFun k305_metric_complex a]
  simp only [Rat.cast_inv, Rat.cast_natCast]

/-- This action is derived from the actual differential H and its true
adjoint creator, after proving that every output remains in the same block. -/
theorem k305_actual_pair_hamiltonian_action (x : Fin 5 → ℂ) :
    canonicalPairHamiltonian9 5 (canonicalBlock (factorialScale 8) k305occ x) =
      canonicalBlock (factorialScale 8) k305occ
        ((complexify p305Ginv * complexify p305rawHform) *ᵥ x) := by
  have h := canonicalPairHamiltonian9_block_action 5 (by decide)
    k305occ k305_occupation_injective p305basis
    (fun a => k305_canonical_source_word a)
    (fun a => (k305_source_length_degree a).1)
    (fun a => (k305_source_length_degree a).2)
    (fun p a => k305_pair_output_membership p a) x
  simpa only [k305_actual_full_inverse, k305_actual_pair_block_form] using h

/-- H applied twice is the original differential operator composed with
itself, justified by its genuine finite-block invariance. -/
theorem k305_actual_pair_hamiltonian_square_form (x y : Fin 5 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k305occ x)
      (canonicalPairHamiltonian9 5
        (canonicalPairHamiltonian9 5 (canonicalBlock (factorialScale 8) k305occ y))) =
      star x ⬝ᵥ ((complexify p305rawHform * complexify p305Ginv *
        complexify p305rawHform) *ᵥ y) := by
  have h := canonicalPairHamiltonian9_block_square 5 (by decide)
    k305occ k305_occupation_injective p305basis
    (fun a => k305_canonical_source_word a)
    (fun a => (k305_source_length_degree a).1)
    (fun a => (k305_source_length_degree a).2)
    (fun p a => k305_pair_output_membership p a) x y
  simpa only [k305_actual_full_inverse, k305_actual_pair_block_form] using h

/-- All nine source degree blocks use one and the same genuine finite H_8.
The extra pair degrees vanish by actual derivative action, not a matrix cutoff. -/
theorem k305_common_pair_hamiltonian (x : Fin 5 → ℂ) :
    canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k305occ x) =
      canonicalPairHamiltonian9 5 (canonicalBlock (factorialScale 8) k305occ x) := by
  simp only [canonicalBlock, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  have ha : scaledWord pairFactorialRoot9 ((p305basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k305occ a) := k305_canonical_source_word a
  simpa only [ha] using canonicalPairHamiltonian9_cutoff_word 5 8 (by decide) (by decide)
    (p305basis a) (k305_source_labels_bounded a)
    (k305_source_length_degree a).1 (k305_source_length_degree a).2

theorem k305_actual_common_pair_hamiltonian_action (x : Fin 5 → ℂ) :
    canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k305occ x) =
      canonicalBlock (factorialScale 8) k305occ
        ((complexify p305Ginv * complexify p305rawHform) *ᵥ x) := by
  rw [k305_common_pair_hamiltonian x, k305_actual_pair_hamiltonian_action x]

theorem k305_actual_common_pair_hamiltonian_form (x y : Fin 5 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k305occ x)
      (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k305occ y)) =
      star x ⬝ᵥ (complexify p305rawHform *ᵥ y) := by
  rw [k305_common_pair_hamiltonian y, actualPairBlock_cross_form, k305_actual_pair_block_form]

theorem k305_actual_common_pair_hamiltonian_square_form (x y : Fin 5 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k305occ x)
      (canonicalPairHamiltonian9 8
        (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k305occ y))) =
      star x ⬝ᵥ ((complexify p305rawHform * complexify p305Ginv *
        complexify p305rawHform) *ᵥ y) := by
  rw [k305_actual_common_pair_hamiltonian_action y,
    k305_actual_common_pair_hamiltonian_form x
      ((complexify p305Ginv * complexify p305rawHform) *ᵥ y)]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

#print axioms k305_common_pair_hamiltonian
#print axioms k305_actual_common_pair_hamiltonian_action
#print axioms k305_actual_common_pair_hamiltonian_form
#print axioms k305_actual_common_pair_hamiltonian_square_form

#print axioms k305_actual_pair_block_form
#print axioms k305_actual_full_inverse
#print axioms k305_actual_pair_hamiltonian_action
#print axioms k305_actual_pair_hamiltonian_square_form
end TorusLean.BosonFiniteCertificate
