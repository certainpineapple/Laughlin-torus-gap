import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Positive coefficient forms for four-body annihilation outputs

This is the finite weighted-coordinate positivity step underlying a positive
few-body lift. It directly reuses `Matrix.PosSemidef.dotProduct_mulVec_nonneg`,
the same PSD step used by pinned OAI `PositiveFockLift`. The latter's
`operatorLift_positive` is specialized to the fermionic `Space Q`, so cannot
serve as a bosonic lift theorem.

The theorem below is conditional: the matrix must be PSD, the weights must be
nonnegative, and the supplied coordinates must still be identified with the
physical four-body annihilation maps and occupation metric. It neither defines
the physical torus Hamiltonian nor closes its positive-lift obligation.
-/

namespace TorusLean.Boson

open scoped BigOperators ComplexOrder
open Matrix

variable {I O : Type*} [Fintype I]

noncomputable def coefficientLiftForm (s : Finset O) (weight : O → ℝ)
    (M : Matrix I I ℂ) (output : I → O → ℂ) : ℝ :=
  ∑ m ∈ s, weight m * (star (fun i => output i m) ⬝ᵥ
    (M *ᵥ (fun i => output i m))).re

/-- PSD coefficients give a positive finite weighted annihilation-output form. -/
theorem coefficientLiftForm_nonneg (s : Finset O) (weight : O → ℝ)
    (M : Matrix I I ℂ) (output : I → O → ℂ)
    (hw : ∀ m ∈ s, 0 ≤ weight m) (hM : M.PosSemidef) :
    0 ≤ coefficientLiftForm s weight M output := by
  unfold coefficientLiftForm
  apply Finset.sum_nonneg
  intro m hm
  exact mul_nonneg (hw m hm)
    (Complex.nonneg_iff.mp (hM.dotProduct_mulVec_nonneg (fun i => output i m))).1

#print axioms coefficientLiftForm_nonneg

end TorusLean.Boson
