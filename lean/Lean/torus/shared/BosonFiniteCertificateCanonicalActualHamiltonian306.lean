import torus.shared.BosonFiniteCertificateCanonicalHamiltonian306
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

theorem k306_actual_pair_block_form :
    actualPairBlockForm 6 k306occ = complexify p306rawHform := by
  have h : actualPairBlockForm 6 k306occ = canonicalPairHamiltonianForm 6 k306occ := by
    ext a b
    exact actualPairBlockForm_pair_forms 6 k306occ a b
  rw [h, k306_actual_H_raw]

theorem k306_inverse_diagonal :
    p306Ginv = Matrix.diagonal (fun a => (k306metric a : ℚ)⁻¹) := by decide +kernel

theorem k306_actual_full_inverse :
    canonicalFullInverseGram k306occ = complexify p306Ginv := by
  rw [k306_inverse_diagonal, complexify_diagonal_rat]
  unfold canonicalFullInverseGram
  apply congrArg Matrix.diagonal
  funext a
  rw [congrFun k306_metric_complex a]
  simp only [Rat.cast_inv, Rat.cast_natCast]

/-- This action is derived from the actual differential H and its true
adjoint creator, after proving that every output remains in the same block. -/
theorem k306_actual_pair_hamiltonian_action (x : Fin 7 → ℂ) :
    canonicalPairHamiltonian9 6 (canonicalBlock (factorialScale 8) k306occ x) =
      canonicalBlock (factorialScale 8) k306occ
        ((complexify p306Ginv * complexify p306rawHform) *ᵥ x) := by
  have h := canonicalPairHamiltonian9_block_action 6 (by decide)
    k306occ k306_occupation_injective p306basis
    (fun a => k306_canonical_source_word a)
    (fun a => (k306_source_length_degree a).1)
    (fun a => (k306_source_length_degree a).2)
    (fun p a => k306_pair_output_membership p a) x
  simpa only [k306_actual_full_inverse, k306_actual_pair_block_form] using h

/-- H applied twice is the original differential operator composed with
itself, justified by its genuine finite-block invariance. -/
theorem k306_actual_pair_hamiltonian_square_form (x y : Fin 7 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k306occ x)
      (canonicalPairHamiltonian9 6
        (canonicalPairHamiltonian9 6 (canonicalBlock (factorialScale 8) k306occ y))) =
      star x ⬝ᵥ ((complexify p306rawHform * complexify p306Ginv *
        complexify p306rawHform) *ᵥ y) := by
  have h := canonicalPairHamiltonian9_block_square 6 (by decide)
    k306occ k306_occupation_injective p306basis
    (fun a => k306_canonical_source_word a)
    (fun a => (k306_source_length_degree a).1)
    (fun a => (k306_source_length_degree a).2)
    (fun p a => k306_pair_output_membership p a) x y
  simpa only [k306_actual_full_inverse, k306_actual_pair_block_form] using h

/-- All nine source degree blocks use one and the same genuine finite H_8.
The extra pair degrees vanish by actual derivative action, not a matrix cutoff. -/
theorem k306_common_pair_hamiltonian (x : Fin 7 → ℂ) :
    canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k306occ x) =
      canonicalPairHamiltonian9 6 (canonicalBlock (factorialScale 8) k306occ x) := by
  simp only [canonicalBlock, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  have ha : scaledWord pairFactorialRoot9 ((p306basis a).map fin9) =
      canonicalMonomial (factorialScale 8) (k306occ a) := k306_canonical_source_word a
  simpa only [ha] using canonicalPairHamiltonian9_cutoff_word 6 8 (by decide) (by decide)
    (p306basis a) (k306_source_labels_bounded a)
    (k306_source_length_degree a).1 (k306_source_length_degree a).2

theorem k306_actual_common_pair_hamiltonian_action (x : Fin 7 → ℂ) :
    canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k306occ x) =
      canonicalBlock (factorialScale 8) k306occ
        ((complexify p306Ginv * complexify p306rawHform) *ᵥ x) := by
  rw [k306_common_pair_hamiltonian x, k306_actual_pair_hamiltonian_action x]

theorem k306_actual_common_pair_hamiltonian_form (x y : Fin 7 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k306occ x)
      (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k306occ y)) =
      star x ⬝ᵥ (complexify p306rawHform *ᵥ y) := by
  rw [k306_common_pair_hamiltonian y, actualPairBlock_cross_form, k306_actual_pair_block_form]

theorem k306_actual_common_pair_hamiltonian_square_form (x y : Fin 7 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k306occ x)
      (canonicalPairHamiltonian9 8
        (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k306occ y))) =
      star x ⬝ᵥ ((complexify p306rawHform * complexify p306Ginv *
        complexify p306rawHform) *ᵥ y) := by
  rw [k306_actual_common_pair_hamiltonian_action y,
    k306_actual_common_pair_hamiltonian_form x
      ((complexify p306Ginv * complexify p306rawHform) *ᵥ y)]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

#print axioms k306_common_pair_hamiltonian
#print axioms k306_actual_common_pair_hamiltonian_action
#print axioms k306_actual_common_pair_hamiltonian_form
#print axioms k306_actual_common_pair_hamiltonian_square_form

#print axioms k306_actual_pair_block_form
#print axioms k306_actual_full_inverse
#print axioms k306_actual_pair_hamiltonian_action
#print axioms k306_actual_pair_hamiltonian_square_form
end TorusLean.BosonFiniteCertificate
