import torus.shared.BosonFiniteCertificateCanonicalHamiltonian307
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

theorem k307_actual_pair_block_form :
    actualPairBlockForm 7 k307occ = complexify p307rawHform := by
  have h : actualPairBlockForm 7 k307occ = canonicalPairHamiltonianForm 7 k307occ := by
    ext a b
    exact actualPairBlockForm_pair_forms 7 k307occ a b
  rw [h, k307_actual_H_raw]

theorem k307_inverse_diagonal :
    p307Ginv = Matrix.diagonal (fun a => (k307metric a : ℚ)⁻¹) := by decide +kernel

theorem k307_actual_full_inverse :
    canonicalFullInverseGram k307occ = complexify p307Ginv := by
  rw [k307_inverse_diagonal, complexify_diagonal_rat]
  unfold canonicalFullInverseGram
  apply congrArg Matrix.diagonal
  funext a
  rw [congrFun k307_metric_complex a]
  simp only [Rat.cast_inv, Rat.cast_natCast]

/-- This action is derived from the actual differential H and its true
adjoint creator, after proving that every output remains in the same block. -/
theorem k307_actual_pair_hamiltonian_action (x : Fin 8 → ℂ) :
    canonicalPairHamiltonian9 7 (canonicalBlock (factorialScale 8) k307occ x) =
      canonicalBlock (factorialScale 8) k307occ
        ((complexify p307Ginv * complexify p307rawHform) *ᵥ x) := by
  have h := canonicalPairHamiltonian9_block_action 7 (by decide)
    k307occ k307_occupation_injective p307basis
    (fun a => k307_canonical_source_word a)
    (fun a => (k307_source_length_degree a).1)
    (fun a => (k307_source_length_degree a).2)
    (fun p a => k307_pair_output_membership p a) x
  simpa only [k307_actual_full_inverse, k307_actual_pair_block_form] using h

/-- H applied twice is the original differential operator composed with
itself, justified by its genuine finite-block invariance. -/
theorem k307_actual_pair_hamiltonian_square_form (x y : Fin 8 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k307occ x)
      (canonicalPairHamiltonian9 7
        (canonicalPairHamiltonian9 7 (canonicalBlock (factorialScale 8) k307occ y))) =
      star x ⬝ᵥ ((complexify p307rawHform * complexify p307Ginv *
        complexify p307rawHform) *ᵥ y) := by
  have h := canonicalPairHamiltonian9_block_square 7 (by decide)
    k307occ k307_occupation_injective p307basis
    (fun a => k307_canonical_source_word a)
    (fun a => (k307_source_length_degree a).1)
    (fun a => (k307_source_length_degree a).2)
    (fun p a => k307_pair_output_membership p a) x y
  simpa only [k307_actual_full_inverse, k307_actual_pair_block_form] using h

/-- All nine source degree blocks use one and the same genuine finite H_8.
The extra pair degrees vanish by actual derivative action, not a matrix cutoff. -/
theorem k307_common_pair_hamiltonian (x : Fin 8 → ℂ) :
    canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k307occ x) =
      canonicalPairHamiltonian9 7 (canonicalBlock (factorialScale 8) k307occ x) := by
  simp only [canonicalBlock, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  have ha : scaledWord pairFactorialRoot9 ((p307basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k307occ a) := k307_canonical_source_word a
  simpa only [ha] using canonicalPairHamiltonian9_cutoff_word 7 8 (by decide) (by decide)
    (p307basis a) (k307_source_labels_bounded a)
    (k307_source_length_degree a).1 (k307_source_length_degree a).2

theorem k307_actual_common_pair_hamiltonian_action (x : Fin 8 → ℂ) :
    canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k307occ x) =
      canonicalBlock (factorialScale 8) k307occ
        ((complexify p307Ginv * complexify p307rawHform) *ᵥ x) := by
  rw [k307_common_pair_hamiltonian x, k307_actual_pair_hamiltonian_action x]

theorem k307_actual_common_pair_hamiltonian_form (x y : Fin 8 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k307occ x)
      (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k307occ y)) =
      star x ⬝ᵥ (complexify p307rawHform *ᵥ y) := by
  rw [k307_common_pair_hamiltonian y, actualPairBlock_cross_form, k307_actual_pair_block_form]

theorem k307_actual_common_pair_hamiltonian_square_form (x y : Fin 8 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k307occ x)
      (canonicalPairHamiltonian9 8
        (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k307occ y))) =
      star x ⬝ᵥ ((complexify p307rawHform * complexify p307Ginv *
        complexify p307rawHform) *ᵥ y) := by
  rw [k307_actual_common_pair_hamiltonian_action y,
    k307_actual_common_pair_hamiltonian_form x
      ((complexify p307Ginv * complexify p307rawHform) *ᵥ y)]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

#print axioms k307_common_pair_hamiltonian
#print axioms k307_actual_common_pair_hamiltonian_action
#print axioms k307_actual_common_pair_hamiltonian_form
#print axioms k307_actual_common_pair_hamiltonian_square_form

#print axioms k307_actual_pair_block_form
#print axioms k307_actual_full_inverse
#print axioms k307_actual_pair_hamiltonian_action
#print axioms k307_actual_pair_hamiltonian_square_form
end TorusLean.BosonFiniteCertificate
