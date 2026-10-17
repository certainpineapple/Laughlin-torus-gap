import torus.shared.BosonFiniteCertificateCanonicalHamiltonian304
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

theorem k304_actual_pair_block_form :
    actualPairBlockForm 4 k304occ = complexify p304rawHform := by
  have h : actualPairBlockForm 4 k304occ = canonicalPairHamiltonianForm 4 k304occ := by
    ext a b
    exact actualPairBlockForm_pair_forms 4 k304occ a b
  rw [h, k304_actual_H_raw]

theorem k304_inverse_diagonal :
    p304Ginv = Matrix.diagonal (fun a => (k304metric a : ℚ)⁻¹) := by decide +kernel

theorem k304_actual_full_inverse :
    canonicalFullInverseGram k304occ = complexify p304Ginv := by
  rw [k304_inverse_diagonal, complexify_diagonal_rat]
  unfold canonicalFullInverseGram
  apply congrArg Matrix.diagonal
  funext a
  rw [congrFun k304_metric_complex a]
  simp only [Rat.cast_inv, Rat.cast_natCast]

/-- This action is derived from the actual differential H and its true
adjoint creator, after proving that every output remains in the same block. -/
theorem k304_actual_pair_hamiltonian_action (x : Fin 4 → ℂ) :
    canonicalPairHamiltonian9 4 (canonicalBlock (factorialScale 8) k304occ x) =
      canonicalBlock (factorialScale 8) k304occ
        ((complexify p304Ginv * complexify p304rawHform) *ᵥ x) := by
  have h := canonicalPairHamiltonian9_block_action 4 (by decide)
    k304occ k304_occupation_injective p304basis
    (fun a => k304_canonical_source_word a)
    (fun a => (k304_source_length_degree a).1)
    (fun a => (k304_source_length_degree a).2)
    (fun p a => k304_pair_output_membership p a) x
  simpa only [k304_actual_full_inverse, k304_actual_pair_block_form] using h

/-- H applied twice is the original differential operator composed with
itself, justified by its genuine finite-block invariance. -/
theorem k304_actual_pair_hamiltonian_square_form (x y : Fin 4 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k304occ x)
      (canonicalPairHamiltonian9 4
        (canonicalPairHamiltonian9 4 (canonicalBlock (factorialScale 8) k304occ y))) =
      star x ⬝ᵥ ((complexify p304rawHform * complexify p304Ginv *
        complexify p304rawHform) *ᵥ y) := by
  have h := canonicalPairHamiltonian9_block_square 4 (by decide)
    k304occ k304_occupation_injective p304basis
    (fun a => k304_canonical_source_word a)
    (fun a => (k304_source_length_degree a).1)
    (fun a => (k304_source_length_degree a).2)
    (fun p a => k304_pair_output_membership p a) x y
  simpa only [k304_actual_full_inverse, k304_actual_pair_block_form] using h

/-- All nine source degree blocks use one and the same genuine finite H_8.
The extra pair degrees vanish by actual derivative action, not a matrix cutoff. -/
theorem k304_common_pair_hamiltonian (x : Fin 4 → ℂ) :
    canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k304occ x) =
      canonicalPairHamiltonian9 4 (canonicalBlock (factorialScale 8) k304occ x) := by
  simp only [canonicalBlock, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  have ha : scaledWord pairFactorialRoot9 ((p304basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k304occ a) := k304_canonical_source_word a
  simpa only [ha] using canonicalPairHamiltonian9_cutoff_word 4 8 (by decide) (by decide)
    (p304basis a) (k304_source_labels_bounded a)
    (k304_source_length_degree a).1 (k304_source_length_degree a).2

theorem k304_actual_common_pair_hamiltonian_action (x : Fin 4 → ℂ) :
    canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k304occ x) =
      canonicalBlock (factorialScale 8) k304occ
        ((complexify p304Ginv * complexify p304rawHform) *ᵥ x) := by
  rw [k304_common_pair_hamiltonian x, k304_actual_pair_hamiltonian_action x]

theorem k304_actual_common_pair_hamiltonian_form (x y : Fin 4 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k304occ x)
      (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k304occ y)) =
      star x ⬝ᵥ (complexify p304rawHform *ᵥ y) := by
  rw [k304_common_pair_hamiltonian y, actualPairBlock_cross_form, k304_actual_pair_block_form]

theorem k304_actual_common_pair_hamiltonian_square_form (x y : Fin 4 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k304occ x)
      (canonicalPairHamiltonian9 8
        (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k304occ y))) =
      star x ⬝ᵥ ((complexify p304rawHform * complexify p304Ginv *
        complexify p304rawHform) *ᵥ y) := by
  rw [k304_actual_common_pair_hamiltonian_action y,
    k304_actual_common_pair_hamiltonian_form x
      ((complexify p304Ginv * complexify p304rawHform) *ᵥ y)]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

#print axioms k304_common_pair_hamiltonian
#print axioms k304_actual_common_pair_hamiltonian_action
#print axioms k304_actual_common_pair_hamiltonian_form
#print axioms k304_actual_common_pair_hamiltonian_square_form

#print axioms k304_actual_pair_block_form
#print axioms k304_actual_full_inverse
#print axioms k304_actual_pair_hamiltonian_action
#print axioms k304_actual_pair_hamiltonian_square_form
end TorusLean.BosonFiniteCertificate
