import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
Algebraic classification of the full integer Fourier coefficient recurrence.
No analytic theta space, Hamiltonian, or physical kernel is defined here.
The nowhere-zero weight is explicit for the Gaussian specialization below.
-/

namespace TorusLean.Geometry.ThetaFactorization

variable {K : Type*} [Field K]

/-- All integer coefficients whose normalized sequence is degree-periodic.
The index is `ℤ`, so this definition imposes no positive or negative cutoff. -/
def coefficientSpace (d : ℕ) (w : ℤ → K) : Submodule K (ℤ → K) where
  carrier := {c | Function.Periodic (fun n => c n / w n) (d : ℤ)}
  zero_mem' := by simp [Function.Periodic]
  add_mem' := by
    intro c e hc he n
    change ∀ n, c (n + d) / w (n + d) = c n / w n at hc
    change ∀ n, e (n + d) / w (n + d) = e n / w n at he
    change (c (n + d) + e (n + d)) / w (n + d) = (c n + e n) / w n
    rw [add_div, add_div, hc n, he n]
  smul_mem' := by
    intro a c hc n
    change ∀ n, c (n + d) / w (n + d) = c n / w n at hc
    change (a * c (n + d)) / w (n + d) = (a * c n) / w n
    rw [mul_div_assoc, mul_div_assoc, hc n]

/-- This definition is equivalent to the usual one-step coefficient recurrence;
invertibility of every weight is an explicit premise, not a dimension premise. -/
theorem mem_coefficientSpace_iff (d : ℕ) (w : ℤ → K) (hw : ∀ n, w n ≠ 0)
    (c : ℤ → K) :
    c ∈ coefficientSpace d w ↔
      ∀ n, c (n + d) = (w (n + d) / w n) * c n := by
  change (∀ n, c (n + d) / w (n + d) = c n / w n) ↔ _
  constructor
  · intro h n
    calc
      c (n + d) = (c (n + d) / w (n + d)) * w (n + d) :=
        (div_mul_cancel₀ _ (hw (n + d))).symm
      _ = (c n / w n) * w (n + d) := by rw [h n]
      _ = (w (n + d) / w n) * c n := by ring
  · intro h n
    rw [h n]
    field_simp [hw]

omit [Field K] in
private theorem periodic_residue (d : ℕ) [NeZero d] (g : ℤ → K)
    (hg : Function.Periodic g (d : ℤ)) (n : ℤ) :
    g ((n : ZMod d).val : ℤ) = g n := by
  rw [ZMod.val_intCast, Int.emod_def]
  simpa [mul_comm] using hg.sub_int_mul_eq (n / d)

/-- Restriction of normalized coefficients to residues, with an explicit
extension back to EVERY integer mode. -/
noncomputable def coefficientEquiv (d : ℕ) [NeZero d] (w : ℤ → K)
    (hw : ∀ n, w n ≠ 0) :
    coefficientSpace d w ≃ₗ[K] (ZMod d → K) where
  toFun c r := c.1 (r.val : ℤ) / w (r.val : ℤ)
  invFun v := ⟨fun n => w n * v (n : ZMod d), by
    intro n
    change (w (n + d) * v ((n + d : ℤ) : ZMod d)) / w (n + d) =
      (w n * v (n : ZMod d)) / w n
    simp [hw, Int.cast_add]⟩
  left_inv c := by
    apply Subtype.ext
    funext n
    change w n * (c.1 ((n : ZMod d).val : ℤ) / w ((n : ZMod d).val : ℤ)) = c.1 n
    have hr : c.1 ((n : ZMod d).val : ℤ) / w ((n : ZMod d).val : ℤ) = c.1 n / w n :=
      periodic_residue d (fun n => c.1 n / w n) c.property n
    rw [hr]
    calc
      w n * (c.1 n / w n) = (c.1 n / w n) * w n := mul_comm _ _
      _ = c.1 n := div_mul_cancel₀ _ (hw n)
  right_inv v := by
    funext r
    change (w (r.val : ℤ) * v ((r.val : ℤ) : ZMod d)) / w (r.val : ℤ) = v r
    simp [hw]
  map_add' c e := by
    funext r
    change (c.1 (r.val : ℤ) + e.1 (r.val : ℤ)) / w (r.val : ℤ) = _
    exact add_div _ _ _
  map_smul' a c := by
    funext r
    change (a * c.1 (r.val : ℤ)) / w (r.val : ℤ) = a * (c.1 (r.val : ℤ) / w (r.val : ℤ))
    exact mul_div_assoc _ _ _

theorem coefficientEquiv_symm_apply (d : ℕ) [NeZero d] (w : ℤ → K)
    (hw : ∀ n, w n ≠ 0) (v : ZMod d → K) (n : ℤ) :
    ((coefficientEquiv d w hw).symm v : ℤ → K) n = w n * v (n : ZMod d) := rfl

/-- Exhaustion: the residue data determines a solution at every integer. -/
theorem coefficients_eq_iff (d : ℕ) [NeZero d] (w : ℤ → K)
    (hw : ∀ n, w n ≠ 0) (c e : coefficientSpace d w) :
    c = e ↔ ∀ r : ZMod d, c.1 (r.val : ℤ) / w (r.val : ℤ) =
      e.1 (r.val : ℤ) / w (r.val : ℤ) := by
  constructor
  · rintro rfl r
    rfl
  · intro h
    apply (coefficientEquiv d w hw).injective
    exact funext h

theorem coefficient_finrank (d : ℕ) [NeZero d] (w : ℤ → K)
    (hw : ∀ n, w n ≠ 0) :
    Module.finrank K (coefficientSpace d w) = d := by
  rw [(coefficientEquiv d w hw).finrank_eq, Module.finrank_pi]
  exact ZMod.card d

/-- Gaussian normalization of the theta Fourier recurrence. Physically
`A = i*pi*tau`, `B = -i*psi2`, `sigma = psi1/(2*pi)`.
This definition alone does not assert convergence of the Fourier series. -/
noncomputable def gaussianWeight (d : ℕ) (A B sigma : ℂ) (n : ℤ) : ℂ :=
  Complex.exp (A * ((n : ℂ) + sigma) ^ 2 / (d : ℂ) + B * (n : ℂ) / (d : ℂ))

theorem gaussianWeight_ne_zero (d : ℕ) (A B sigma : ℂ) (n : ℤ) :
    gaussianWeight d A B sigma n ≠ 0 := Complex.exp_ne_zero _

theorem gaussianWeight_step (d : ℕ) [NeZero d] (A B sigma : ℂ) (n : ℤ) :
    gaussianWeight d A B sigma (n + d) / gaussianWeight d A B sigma n =
      Complex.exp (A * (2 * ((n : ℂ) + sigma) + (d : ℂ)) + B) := by
  unfold gaussianWeight
  rw [← Complex.exp_sub]
  congr 1
  push_cast
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  field_simp [hd]
  ring

/-- The full one-step degree-d theta coefficient equation, as a submodule. -/
def thetaRecurrenceSpace (d : ℕ) (A B sigma : ℂ) : Submodule ℂ (ℤ → ℂ) where
  carrier := {c | ∀ n, c (n + d) =
    Complex.exp (A * (2 * ((n : ℂ) + sigma) + (d : ℂ)) + B) * c n}
  zero_mem' := by simp
  add_mem' := by
    intro c e hc he n
    change c (n + d) + e (n + d) =
      Complex.exp (A * (2 * ((n : ℂ) + sigma) + (d : ℂ)) + B) * (c n + e n)
    rw [hc n, he n]
    exact (mul_add _ _ _).symm
  smul_mem' := by
    intro a c hc n
    change a * c (n + d) =
      Complex.exp (A * (2 * ((n : ℂ) + sigma) + (d : ℂ)) + B) * (a * c n)
    rw [hc n]
    ring

/-- Exact coefficient form of the second theta boundary multiplier.
With `A=i*pi*tau` and `B=-i*psi2`, the left side is translation by tau
and the right side is `exp(i*psi2-i*pi*d*tau)` times the degree-d shift.
This is coefficient algebra, without an unproved interchange of series. -/
theorem theta_multiplier_coefficients_iff (d : ℕ) (A B sigma : ℂ) (c : ℤ → ℂ) :
    c ∈ thetaRecurrenceSpace d A B sigma ↔
      ∀ n : ℤ, Complex.exp (2 * A * ((n : ℂ) + sigma)) * c n =
        Complex.exp (-B - A * (d : ℂ)) * c (n + d) := by
  change (∀ n, c (n + d) =
    Complex.exp (A * (2 * ((n : ℂ) + sigma) + (d : ℂ)) + B) * c n) ↔ _
  have hphase (n : ℤ) : Complex.exp (-B - A * (d : ℂ)) *
      Complex.exp (A * (2 * ((n : ℂ) + sigma) + (d : ℂ)) + B) =
        Complex.exp (2 * A * ((n : ℂ) + sigma)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  constructor
  · intro h n
    rw [h n, ← mul_assoc, hphase n]
  · intro h n
    apply mul_left_cancel₀ (Complex.exp_ne_zero (-B - A * (d : ℂ)))
    rw [← mul_assoc, hphase n]
    exact (h n).symm

theorem thetaRecurrenceSpace_eq (d : ℕ) [NeZero d] (A B sigma : ℂ) :
    thetaRecurrenceSpace d A B sigma = coefficientSpace d (gaussianWeight d A B sigma) := by
  ext c
  change (∀ n, c (n + d) =
    Complex.exp (A * (2 * ((n : ℂ) + sigma) + (d : ℂ)) + B) * c n) ↔
      c ∈ coefficientSpace d (gaussianWeight d A B sigma)
  rw [mem_coefficientSpace_iff d _ (gaussianWeight_ne_zero d A B sigma)]
  simp only [gaussianWeight_step]

/-- Existence and exhaustion for the explicit theta coefficient equation. -/
noncomputable def thetaCoefficientEquiv (d : ℕ) [NeZero d] (A B sigma : ℂ) :
    thetaRecurrenceSpace d A B sigma ≃ₗ[ℂ] (ZMod d → ℂ) :=
  (LinearEquiv.ofEq _ _ (thetaRecurrenceSpace_eq d A B sigma)).trans
    (coefficientEquiv d _ (gaussianWeight_ne_zero d A B sigma))

/-- General degree: dimension is derived from recurrence classification. -/
theorem thetaRecurrence_finrank (d : ℕ) [NeZero d] (A B sigma : ℂ) :
    Module.finrank ℂ (thetaRecurrenceSpace d A B sigma) = d := by
  rw [(thetaCoefficientEquiv d A B sigma).finrank_eq, Module.finrank_pi]
  exact ZMod.card d

/-- This is the coefficient-space dimension bridge for the fermionic degree.
It is NOT a theorem about the physical Hamiltonian's kernel. -/
theorem degree_three_coefficient_finrank (A B sigma : ℂ) :
    Module.finrank ℂ (thetaRecurrenceSpace 3 A B sigma) = 3 :=
  thetaRecurrence_finrank 3 A B sigma

end TorusLean.Geometry.ThetaFactorization
