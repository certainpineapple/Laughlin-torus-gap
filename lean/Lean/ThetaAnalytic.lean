import ThetaFactorization
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable

set_option autoImplicit false

/-!
The analytic realization of each full bilateral residue-class Fourier series.
The parameters `sigma` and `psi` may be complex; real twists are a specialization.
Only `0 < tau.im` and positive degree are used for convergence. No physical
Hamiltonian or completeness theorem for arbitrary holomorphic sections occurs here.
-/

noncomputable section

namespace TorusLean.Geometry.ThetaAnalytic

open Complex Real
open ThetaFactorization

def physicalWeight (d : ℕ) (tau sigma psi : ℂ) (n : ℤ) : ℂ :=
  gaussianWeight d (π * I * tau) (-I * psi) sigma n

def fourierTerm (d : ℕ) (tau sigma psi z : ℂ) (n : ℤ) : ℂ :=
  physicalWeight d tau sigma psi n * exp (2 * π * I * ((n : ℂ) + sigma) * z)

def residueTerm (d : ℕ) (tau sigma psi : ℂ) (r : ℤ) (z : ℂ) (k : ℤ) : ℂ :=
  fourierTerm d tau sigma psi z (r + (d : ℤ) * k)

def thetaArgument (d : ℕ) (tau sigma psi : ℂ) (r : ℤ) (z : ℂ) : ℂ :=
  (d : ℂ) * z + tau * ((r : ℂ) + sigma) - psi / (2 * π)

def residueSection (d : ℕ) (tau sigma psi : ℂ) (r : ℤ) (z : ℂ) : ℂ :=
  fourierTerm d tau sigma psi z r *
    jacobiTheta₂ (thetaArgument d tau sigma psi r z) ((d : ℂ) * tau)

theorem scaled_tau_im_pos (d : ℕ) [NeZero d] (tau : ℂ) (hτ : 0 < tau.im) :
    0 < ((d : ℂ) * tau).im := by
  simpa using mul_pos (show 0 < (d : ℝ) by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)) hτ

theorem residueTerm_eq_thetaTerm (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (r : ℤ) (z : ℂ) (k : ℤ) :
    residueTerm d tau sigma psi r z k = fourierTerm d tau sigma psi z r *
      jacobiTheta₂_term k (thetaArgument d tau sigma psi r z) ((d : ℂ) * tau) := by
  unfold residueTerm fourierTerm physicalWeight gaussianWeight jacobiTheta₂_term thetaArgument
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hp : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp [hd, hp]
  ring

/-- Absolute convergence of both tails, indexed by every integer `k`. -/
theorem residueTerm_summable (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (r : ℤ) (z : ℂ) :
    Summable (residueTerm d tau sigma psi r z) := by
  change Summable (fun k : ℤ => residueTerm d tau sigma psi r z k)
  simp_rw [residueTerm_eq_thetaTerm]
  exact ((summable_jacobiTheta₂_term_iff _ _).mpr (scaled_tau_im_pos d tau hτ)).mul_left _

theorem residueTerm_norm_summable (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (r : ℤ) (z : ℂ) :
    Summable (fun k : ℤ => ‖residueTerm d tau sigma psi r z k‖) :=
  (residueTerm_summable d tau sigma psi hτ r z).norm

/-- This is equality with a convergent bilateral Fourier sum, rather than
a definition of a function with unproved convergence. -/
theorem residueTerm_hasSum (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (r : ℤ) (z : ℂ) :
    HasSum (residueTerm d tau sigma psi r z) (residueSection d tau sigma psi r z) := by
  change HasSum (fun k : ℤ => residueTerm d tau sigma psi r z k) _
  simp_rw [residueTerm_eq_thetaTerm]
  exact (hasSum_jacobiTheta₂_term _ (scaled_tau_im_pos d tau hτ)).mul_left _

theorem residueTerm_tsum (d : ℕ) [NeZero d] (tau sigma psi : ℂ)
    (hτ : 0 < tau.im) (r : ℤ) (z : ℂ) :
    (∑' k : ℤ, residueTerm d tau sigma psi r z k) = residueSection d tau sigma psi r z :=
  (residueTerm_hasSum d tau sigma psi hτ r z).tsum_eq

end TorusLean.Geometry.ThetaAnalytic
