import ThetaAnalytic

set_option autoImplicit false

/-!
Analyticity and the exact torus automorphy factors of the convergent residue
series constructed in `ThetaAnalytic`.  The proofs use the existing two-variable
Jacobi theta differentiability and translation theorems.  No completeness of
arbitrary holomorphic sections or identification with a Hamiltonian kernel is
assumed.
-/

noncomputable section

namespace TorusLean.Geometry.ThetaAnalytic

open Complex Real

lemma jacobiTheta₂_add_nat (z tau : ℂ) (n : ℕ) :
    jacobiTheta₂ (z + (n : ℂ)) tau = jacobiTheta₂ z tau := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add_one, ← add_assoc, jacobiTheta₂_add_left, ih]

theorem thetaArgument_differentiable (d : ℕ) (tau sigma psi : ℂ) (r : ℤ) :
    Differentiable ℂ (thetaArgument d tau sigma psi r) := by
  unfold thetaArgument
  fun_prop

theorem fourierTerm_differentiable (d : ℕ) (tau sigma psi : ℂ) (n : ℤ) :
    Differentiable ℂ (fun z => fourierTerm d tau sigma psi z n) := by
  unfold fourierTerm
  fun_prop

/-- Every convergent residue series is an entire function of its coordinate. -/
theorem residueSection_differentiable (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (r : ℤ) :
    Differentiable ℂ (residueSection d tau sigma psi r) := by
  intro z
  unfold residueSection
  apply (fourierTerm_differentiable d tau sigma psi r z).mul
  exact (differentiableAt_jacobiTheta₂_fst _ (scaled_tau_im_pos d tau hτ)).comp z
    (thetaArgument_differentiable d tau sigma psi r z)

lemma fourierTerm_add_one (d : ℕ) (tau sigma psi z : ℂ) (n : ℤ) :
    fourierTerm d tau sigma psi (z + 1) n =
      exp (2 * π * I * sigma) * fourierTerm d tau sigma psi z n := by
  have he : exp (2 * π * I * ((n : ℂ) + sigma)) = exp (2 * π * I * sigma) := by
    rw [mul_add, Complex.exp_add]
    rw [show 2 * π * I * (n : ℂ) = (n : ℂ) * (2 * π * I) by ring]
    simp only [exp_int_mul_two_pi_mul_I, one_mul]
  unfold fourierTerm
  rw [mul_add, mul_one, Complex.exp_add, he]
  ring

lemma thetaArgument_add_one (d : ℕ) (tau sigma psi z : ℂ) (r : ℤ) :
    thetaArgument d tau sigma psi r (z + 1) =
      thetaArgument d tau sigma psi r z + (d : ℂ) := by
  unfold thetaArgument
  ring

/-- The exact unit-cycle twist, with complex twists allowed as well. -/
theorem residueSection_add_one (d : ℕ) (tau sigma psi z : ℂ) (r : ℤ) :
    residueSection d tau sigma psi r (z + 1) =
      exp (2 * π * I * sigma) * residueSection d tau sigma psi r z := by
  unfold residueSection
  rw [fourierTerm_add_one, thetaArgument_add_one, jacobiTheta₂_add_nat]
  ring

lemma thetaArgument_add_tau (d : ℕ) (tau sigma psi z : ℂ) (r : ℤ) :
    thetaArgument d tau sigma psi r (z + tau) =
      thetaArgument d tau sigma psi r z + (d : ℂ) * tau := by
  unfold thetaArgument
  ring

/-- The exact second-cycle multiplier of a degree `d` section. -/
theorem residueSection_add_tau (d : ℕ) (tau sigma psi z : ℂ) (r : ℤ) :
    residueSection d tau sigma psi r (z + tau) =
      exp (I * psi - π * I * (d : ℂ) * tau - 2 * π * I * (d : ℂ) * z) *
        residueSection d tau sigma psi r z := by
  unfold residueSection
  rw [thetaArgument_add_tau, jacobiTheta₂_add_left']
  unfold fourierTerm
  rw [mul_add, Complex.exp_add]
  have he :
      2 * π * I * ((r : ℂ) + sigma) * tau +
          (-π * I * ((d : ℂ) * tau + 2 * thetaArgument d tau sigma psi r z)) =
        I * psi - π * I * (d : ℂ) * tau - 2 * π * I * (d : ℂ) * z := by
    unfold thetaArgument
    have hp : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    field_simp [hp]
    ring
  calc
    _ = physicalWeight d tau sigma psi r * exp (2 * π * I * ((r : ℂ) + sigma) * z) *
        (exp (2 * π * I * ((r : ℂ) + sigma) * tau) *
          exp (-π * I * ((d : ℂ) * tau + 2 * thetaArgument d tau sigma psi r z))) *
          jacobiTheta₂ (thetaArgument d tau sigma psi r z) ((d : ℂ) * tau) := by ring
    _ = _ := by rw [← Complex.exp_add, he]; ring

/-- Real twists specialize the same entire functions without extra hypotheses. -/
theorem residueSection_real_twists_differentiable (d : ℕ) [NeZero d] (tau : ℂ)
    (sigma psi : ℝ) (hτ : 0 < tau.im) (r : ℤ) :
    Differentiable ℂ (residueSection d tau sigma psi r) :=
  residueSection_differentiable d tau sigma psi hτ r

end TorusLean.Geometry.ThetaAnalytic
