import torus.shared.BosonFiniteCertificateCanonicalHamiltonian302
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

theorem k302_actual_pair_block_form :
    actualPairBlockForm 2 k302occ = complexify p302rawHform := by
  have h : actualPairBlockForm 2 k302occ = canonicalPairHamiltonianForm 2 k302occ := by
    ext a b
    exact actualPairBlockForm_pair_forms 2 k302occ a b
  rw [h, k302_actual_H_raw]

theorem k302_inverse_diagonal :
    p302Ginv = Matrix.diagonal (fun a => (k302metric a : ℚ)⁻¹) := by decide +kernel

theorem k302_actual_full_inverse :
    canonicalFullInverseGram k302occ = complexify p302Ginv := by
  rw [k302_inverse_diagonal, complexify_diagonal_rat]
  unfold canonicalFullInverseGram
  apply congrArg Matrix.diagonal
  funext a
  rw [congrFun k302_metric_complex a]
  simp only [Rat.cast_inv, Rat.cast_natCast]

/-- This action is derived from the actual differential H and its true
adjoint creator, after proving that every output remains in the same block. -/
theorem k302_actual_pair_hamiltonian_action (x : Fin 2 → ℂ) :
    canonicalPairHamiltonian9 2 (canonicalBlock (factorialScale 8) k302occ x) =
      canonicalBlock (factorialScale 8) k302occ
        ((complexify p302Ginv * complexify p302rawHform) *ᵥ x) := by
  have h := canonicalPairHamiltonian9_block_action 2 (by decide)
    k302occ k302_occupation_injective p302basis
    (fun a => k302_canonical_source_word a)
    (fun a => (k302_source_length_degree a).1)
    (fun a => (k302_source_length_degree a).2)
    (fun p a => k302_pair_output_membership p a) x
  simpa only [k302_actual_full_inverse, k302_actual_pair_block_form] using h

/-- H applied twice is the original differential operator composed with
itself, justified by its genuine finite-block invariance. -/
theorem k302_actual_pair_hamiltonian_square_form (x y : Fin 2 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k302occ x)
      (canonicalPairHamiltonian9 2
        (canonicalPairHamiltonian9 2 (canonicalBlock (factorialScale 8) k302occ y))) =
      star x ⬝ᵥ ((complexify p302rawHform * complexify p302Ginv *
        complexify p302rawHform) *ᵥ y) := by
  have h := canonicalPairHamiltonian9_block_square 2 (by decide)
    k302occ k302_occupation_injective p302basis
    (fun a => k302_canonical_source_word a)
    (fun a => (k302_source_length_degree a).1)
    (fun a => (k302_source_length_degree a).2)
    (fun p a => k302_pair_output_membership p a) x y
  simpa only [k302_actual_full_inverse, k302_actual_pair_block_form] using h

/-- All nine source degree blocks use one and the same genuine finite H_8.
The extra pair degrees vanish by actual derivative action, not a matrix cutoff. -/
theorem k302_common_pair_hamiltonian (x : Fin 2 → ℂ) :
    canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k302occ x) =
      canonicalPairHamiltonian9 2 (canonicalBlock (factorialScale 8) k302occ x) := by
  simp only [canonicalBlock, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  have ha : scaledWord pairFactorialRoot9 ((p302basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k302occ a) := k302_canonical_source_word a
  simpa only [ha] using canonicalPairHamiltonian9_cutoff_word 2 8 (by decide) (by decide)
    (p302basis a) (k302_source_labels_bounded a)
    (k302_source_length_degree a).1 (k302_source_length_degree a).2

theorem k302_actual_common_pair_hamiltonian_action (x : Fin 2 → ℂ) :
    canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k302occ x) =
      canonicalBlock (factorialScale 8) k302occ
        ((complexify p302Ginv * complexify p302rawHform) *ᵥ x) := by
  rw [k302_common_pair_hamiltonian x, k302_actual_pair_hamiltonian_action x]

theorem k302_actual_common_pair_hamiltonian_form (x y : Fin 2 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k302occ x)
      (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k302occ y)) =
      star x ⬝ᵥ (complexify p302rawHform *ᵥ y) := by
  rw [k302_common_pair_hamiltonian y, actualPairBlock_cross_form, k302_actual_pair_block_form]

theorem k302_actual_common_pair_hamiltonian_square_form (x y : Fin 2 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k302occ x)
      (canonicalPairHamiltonian9 8
        (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k302occ y))) =
      star x ⬝ᵥ ((complexify p302rawHform * complexify p302Ginv *
        complexify p302rawHform) *ᵥ y) := by
  rw [k302_actual_common_pair_hamiltonian_action y,
    k302_actual_common_pair_hamiltonian_form x
      ((complexify p302Ginv * complexify p302rawHform) *ᵥ y)]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

#print axioms k302_common_pair_hamiltonian
#print axioms k302_actual_common_pair_hamiltonian_action
#print axioms k302_actual_common_pair_hamiltonian_form
#print axioms k302_actual_common_pair_hamiltonian_square_form

#print axioms k302_actual_pair_block_form
#print axioms k302_actual_full_inverse
#print axioms k302_actual_pair_hamiltonian_action
#print axioms k302_actual_pair_hamiltonian_square_form
end TorusLean.BosonFiniteCertificate
