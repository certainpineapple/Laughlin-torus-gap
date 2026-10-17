import torus.shared.BosonFiniteCertificateCanonicalHamiltonian300
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

theorem k300_actual_pair_block_form :
    actualPairBlockForm 0 k300occ = complexify p300rawHform := by
  have h : actualPairBlockForm 0 k300occ = canonicalPairHamiltonianForm 0 k300occ := by
    ext a b
    exact actualPairBlockForm_pair_forms 0 k300occ a b
  rw [h, k300_actual_H_raw]

theorem k300_inverse_diagonal :
    p300Ginv = Matrix.diagonal (fun a => (k300metric a : ℚ)⁻¹) := by decide +kernel

theorem k300_actual_full_inverse :
    canonicalFullInverseGram k300occ = complexify p300Ginv := by
  rw [k300_inverse_diagonal, complexify_diagonal_rat]
  unfold canonicalFullInverseGram
  apply congrArg Matrix.diagonal
  funext a
  rw [congrFun k300_metric_complex a]
  simp only [Rat.cast_inv, Rat.cast_natCast]

/-- This action is derived from the actual differential H and its true
adjoint creator, after proving that every output remains in the same block. -/
theorem k300_actual_pair_hamiltonian_action (x : Fin 1 → ℂ) :
    canonicalPairHamiltonian9 0 (canonicalBlock (factorialScale 8) k300occ x) =
      canonicalBlock (factorialScale 8) k300occ
        ((complexify p300Ginv * complexify p300rawHform) *ᵥ x) := by
  have h := canonicalPairHamiltonian9_block_action 0 (by decide)
    k300occ k300_occupation_injective p300basis
    (fun a => k300_canonical_source_word a)
    (fun a => (k300_source_length_degree a).1)
    (fun a => (k300_source_length_degree a).2)
    (fun p a => k300_pair_output_membership p a) x
  simpa only [k300_actual_full_inverse, k300_actual_pair_block_form] using h

/-- H applied twice is the original differential operator composed with
itself, justified by its genuine finite-block invariance. -/
theorem k300_actual_pair_hamiltonian_square_form (x y : Fin 1 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k300occ x)
      (canonicalPairHamiltonian9 0
        (canonicalPairHamiltonian9 0 (canonicalBlock (factorialScale 8) k300occ y))) =
      star x ⬝ᵥ ((complexify p300rawHform * complexify p300Ginv *
        complexify p300rawHform) *ᵥ y) := by
  have h := canonicalPairHamiltonian9_block_square 0 (by decide)
    k300occ k300_occupation_injective p300basis
    (fun a => k300_canonical_source_word a)
    (fun a => (k300_source_length_degree a).1)
    (fun a => (k300_source_length_degree a).2)
    (fun p a => k300_pair_output_membership p a) x y
  simpa only [k300_actual_full_inverse, k300_actual_pair_block_form] using h

/-- All nine source degree blocks use one and the same genuine finite H_8.
The extra pair degrees vanish by actual derivative action, not a matrix cutoff. -/
theorem k300_common_pair_hamiltonian (x : Fin 1 → ℂ) :
    canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k300occ x) =
      canonicalPairHamiltonian9 0 (canonicalBlock (factorialScale 8) k300occ x) := by
  simp only [canonicalBlock, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  have ha : scaledWord pairFactorialRoot9 ((p300basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k300occ a) := k300_canonical_source_word a
  simpa only [ha] using canonicalPairHamiltonian9_cutoff_word 0 8 (by decide) (by decide)
    (p300basis a) (k300_source_labels_bounded a)
    (k300_source_length_degree a).1 (k300_source_length_degree a).2

theorem k300_actual_common_pair_hamiltonian_action (x : Fin 1 → ℂ) :
    canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k300occ x) =
      canonicalBlock (factorialScale 8) k300occ
        ((complexify p300Ginv * complexify p300rawHform) *ᵥ x) := by
  rw [k300_common_pair_hamiltonian x, k300_actual_pair_hamiltonian_action x]

theorem k300_actual_common_pair_hamiltonian_form (x y : Fin 1 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k300occ x)
      (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k300occ y)) =
      star x ⬝ᵥ (complexify p300rawHform *ᵥ y) := by
  rw [k300_common_pair_hamiltonian y, actualPairBlock_cross_form, k300_actual_pair_block_form]

theorem k300_actual_common_pair_hamiltonian_square_form (x y : Fin 1 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k300occ x)
      (canonicalPairHamiltonian9 8
        (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k300occ y))) =
      star x ⬝ᵥ ((complexify p300rawHform * complexify p300Ginv *
        complexify p300rawHform) *ᵥ y) := by
  rw [k300_actual_common_pair_hamiltonian_action y,
    k300_actual_common_pair_hamiltonian_form x
      ((complexify p300Ginv * complexify p300rawHform) *ᵥ y)]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

#print axioms k300_common_pair_hamiltonian
#print axioms k300_actual_common_pair_hamiltonian_action
#print axioms k300_actual_common_pair_hamiltonian_form
#print axioms k300_actual_common_pair_hamiltonian_square_form

#print axioms k300_actual_pair_block_form
#print axioms k300_actual_full_inverse
#print axioms k300_actual_pair_hamiltonian_action
#print axioms k300_actual_pair_hamiltonian_square_form
end TorusLean.BosonFiniteCertificate
