import torus.shared.BosonFiniteCertificateCanonicalHamiltonian301
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

theorem k301_actual_pair_block_form :
    actualPairBlockForm 1 k301occ = complexify p301rawHform := by
  have h : actualPairBlockForm 1 k301occ = canonicalPairHamiltonianForm 1 k301occ := by
    ext a b
    exact actualPairBlockForm_pair_forms 1 k301occ a b
  rw [h, k301_actual_H_raw]

theorem k301_inverse_diagonal :
    p301Ginv = Matrix.diagonal (fun a => (k301metric a : ℚ)⁻¹) := by decide +kernel

theorem k301_actual_full_inverse :
    canonicalFullInverseGram k301occ = complexify p301Ginv := by
  rw [k301_inverse_diagonal, complexify_diagonal_rat]
  unfold canonicalFullInverseGram
  apply congrArg Matrix.diagonal
  funext a
  rw [congrFun k301_metric_complex a]
  simp only [Rat.cast_inv, Rat.cast_natCast]

/-- This action is derived from the actual differential H and its true
adjoint creator, after proving that every output remains in the same block. -/
theorem k301_actual_pair_hamiltonian_action (x : Fin 1 → ℂ) :
    canonicalPairHamiltonian9 1 (canonicalBlock (factorialScale 8) k301occ x) =
      canonicalBlock (factorialScale 8) k301occ
        ((complexify p301Ginv * complexify p301rawHform) *ᵥ x) := by
  have h := canonicalPairHamiltonian9_block_action 1 (by decide)
    k301occ k301_occupation_injective p301basis
    (fun a => k301_canonical_source_word a)
    (fun a => (k301_source_length_degree a).1)
    (fun a => (k301_source_length_degree a).2)
    (fun p a => k301_pair_output_membership p a) x
  simpa only [k301_actual_full_inverse, k301_actual_pair_block_form] using h

/-- H applied twice is the original differential operator composed with
itself, justified by its genuine finite-block invariance. -/
theorem k301_actual_pair_hamiltonian_square_form (x y : Fin 1 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k301occ x)
      (canonicalPairHamiltonian9 1
        (canonicalPairHamiltonian9 1 (canonicalBlock (factorialScale 8) k301occ y))) =
      star x ⬝ᵥ ((complexify p301rawHform * complexify p301Ginv *
        complexify p301rawHform) *ᵥ y) := by
  have h := canonicalPairHamiltonian9_block_square 1 (by decide)
    k301occ k301_occupation_injective p301basis
    (fun a => k301_canonical_source_word a)
    (fun a => (k301_source_length_degree a).1)
    (fun a => (k301_source_length_degree a).2)
    (fun p a => k301_pair_output_membership p a) x y
  simpa only [k301_actual_full_inverse, k301_actual_pair_block_form] using h

/-- All nine source degree blocks use one and the same genuine finite H_8.
The extra pair degrees vanish by actual derivative action, not a matrix cutoff. -/
theorem k301_common_pair_hamiltonian (x : Fin 1 → ℂ) :
    canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k301occ x) =
      canonicalPairHamiltonian9 1 (canonicalBlock (factorialScale 8) k301occ x) := by
  simp only [canonicalBlock, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  have ha : scaledWord pairFactorialRoot9 ((p301basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k301occ a) := k301_canonical_source_word a
  simpa only [ha] using canonicalPairHamiltonian9_cutoff_word 1 8 (by decide) (by decide)
    (p301basis a) (k301_source_labels_bounded a)
    (k301_source_length_degree a).1 (k301_source_length_degree a).2

theorem k301_actual_common_pair_hamiltonian_action (x : Fin 1 → ℂ) :
    canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k301occ x) =
      canonicalBlock (factorialScale 8) k301occ
        ((complexify p301Ginv * complexify p301rawHform) *ᵥ x) := by
  rw [k301_common_pair_hamiltonian x, k301_actual_pair_hamiltonian_action x]

theorem k301_actual_common_pair_hamiltonian_form (x y : Fin 1 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k301occ x)
      (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k301occ y)) =
      star x ⬝ᵥ (complexify p301rawHform *ᵥ y) := by
  rw [k301_common_pair_hamiltonian y, actualPairBlock_cross_form, k301_actual_pair_block_form]

theorem k301_actual_common_pair_hamiltonian_square_form (x y : Fin 1 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k301occ x)
      (canonicalPairHamiltonian9 8
        (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k301occ y))) =
      star x ⬝ᵥ ((complexify p301rawHform * complexify p301Ginv *
        complexify p301rawHform) *ᵥ y) := by
  rw [k301_actual_common_pair_hamiltonian_action y,
    k301_actual_common_pair_hamiltonian_form x
      ((complexify p301Ginv * complexify p301rawHform) *ᵥ y)]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

#print axioms k301_common_pair_hamiltonian
#print axioms k301_actual_common_pair_hamiltonian_action
#print axioms k301_actual_common_pair_hamiltonian_form
#print axioms k301_actual_common_pair_hamiltonian_square_form

#print axioms k301_actual_pair_block_form
#print axioms k301_actual_full_inverse
#print axioms k301_actual_pair_hamiltonian_action
#print axioms k301_actual_pair_hamiltonian_square_form
end TorusLean.BosonFiniteCertificate
