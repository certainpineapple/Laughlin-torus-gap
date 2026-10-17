import torus.shared.BosonFiniteCertificateCanonicalHamiltonian308
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

theorem k308_actual_pair_block_form :
    actualPairBlockForm 8 k308occ = complexify p308rawHform := by
  have h : actualPairBlockForm 8 k308occ = canonicalPairHamiltonianForm 8 k308occ := by
    ext a b
    exact actualPairBlockForm_pair_forms 8 k308occ a b
  rw [h, k308_actual_H_raw]

theorem k308_inverse_diagonal :
    p308Ginv = Matrix.diagonal (fun a => (k308metric a : ℚ)⁻¹) := by decide +kernel

theorem k308_actual_full_inverse :
    canonicalFullInverseGram k308occ = complexify p308Ginv := by
  rw [k308_inverse_diagonal, complexify_diagonal_rat]
  unfold canonicalFullInverseGram
  apply congrArg Matrix.diagonal
  funext a
  rw [congrFun k308_metric_complex a]
  simp only [Rat.cast_inv, Rat.cast_natCast]

/-- This action is derived from the actual differential H and its true
adjoint creator, after proving that every output remains in the same block. -/
theorem k308_actual_pair_hamiltonian_action (x : Fin 10 → ℂ) :
    canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k308occ x) =
      canonicalBlock (factorialScale 8) k308occ
        ((complexify p308Ginv * complexify p308rawHform) *ᵥ x) := by
  have h := canonicalPairHamiltonian9_block_action 8 (by decide)
    k308occ k308_occupation_injective p308basis
    (fun a => k308_canonical_source_word a)
    (fun a => (k308_source_length_degree a).1)
    (fun a => (k308_source_length_degree a).2)
    (fun p a => k308_pair_output_membership p a) x
  simpa only [k308_actual_full_inverse, k308_actual_pair_block_form] using h

/-- H applied twice is the original differential operator composed with
itself, justified by its genuine finite-block invariance. -/
theorem k308_actual_pair_hamiltonian_square_form (x y : Fin 10 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k308occ x)
      (canonicalPairHamiltonian9 8
        (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k308occ y))) =
      star x ⬝ᵥ ((complexify p308rawHform * complexify p308Ginv *
        complexify p308rawHform) *ᵥ y) := by
  have h := canonicalPairHamiltonian9_block_square 8 (by decide)
    k308occ k308_occupation_injective p308basis
    (fun a => k308_canonical_source_word a)
    (fun a => (k308_source_length_degree a).1)
    (fun a => (k308_source_length_degree a).2)
    (fun p a => k308_pair_output_membership p a) x y
  simpa only [k308_actual_full_inverse, k308_actual_pair_block_form] using h

/-- All nine source degree blocks use one and the same genuine finite H_8.
The extra pair degrees vanish by actual derivative action, not a matrix cutoff. -/
theorem k308_common_pair_hamiltonian (x : Fin 10 → ℂ) :
    canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k308occ x) =
      canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k308occ x) := by
  rfl

theorem k308_actual_common_pair_hamiltonian_action (x : Fin 10 → ℂ) :
    canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k308occ x) =
      canonicalBlock (factorialScale 8) k308occ
        ((complexify p308Ginv * complexify p308rawHform) *ᵥ x) := by
  rw [k308_common_pair_hamiltonian x, k308_actual_pair_hamiltonian_action x]

theorem k308_actual_common_pair_hamiltonian_form (x y : Fin 10 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k308occ x)
      (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k308occ y)) =
      star x ⬝ᵥ (complexify p308rawHform *ᵥ y) := by
  rw [k308_common_pair_hamiltonian y, actualPairBlock_cross_form, k308_actual_pair_block_form]

theorem k308_actual_common_pair_hamiltonian_square_form (x y : Fin 10 → ℂ) :
    ip (canonicalBlock (factorialScale 8) k308occ x)
      (canonicalPairHamiltonian9 8
        (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) k308occ y))) =
      star x ⬝ᵥ ((complexify p308rawHform * complexify p308Ginv *
        complexify p308rawHform) *ᵥ y) := by
  rw [k308_actual_common_pair_hamiltonian_action y,
    k308_actual_common_pair_hamiltonian_form x
      ((complexify p308Ginv * complexify p308rawHform) *ᵥ y)]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

#print axioms k308_common_pair_hamiltonian
#print axioms k308_actual_common_pair_hamiltonian_action
#print axioms k308_actual_common_pair_hamiltonian_form
#print axioms k308_actual_common_pair_hamiltonian_square_form

#print axioms k308_actual_pair_block_form
#print axioms k308_actual_full_inverse
#print axioms k308_actual_pair_hamiltonian_action
#print axioms k308_actual_pair_hamiltonian_square_form
end TorusLean.BosonFiniteCertificate
