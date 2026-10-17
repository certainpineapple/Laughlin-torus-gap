/- Weighted anchored convergence and an integral-to-energy tail bridge.
   The exact magnetic unfolding/COM partial-trace identity is still an obligation. -/
import UniformTail
import Mathlib.Analysis.Real.Sqrt
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
noncomputable section

namespace TorusLean.Fermion.AnchoredThreeBody
open scoped BigOperators
open Filter Topology MeasureTheory
open UniformTail

/-- Polynomial growth of a periodization/lift map preserves exponential summability.
    The constant may depend on a fixed sector; this theorem is not an N-uniform estimate. -/
theorem summable_polynomial_geometric_bound {V : Type*}
    [NormedAddCommGroup V] [CompleteSpace V] {blocks : ℕ → V}
    {C ρ : ℝ} (shift k : ℕ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hb : ∀ n, ‖blocks n‖ ≤ C * ((n+shift : ℕ) : ℝ)^k * ρ^n) :
    Summable blocks := by
  have hnorm : ‖ρ‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hρ0]
  have hp := (summable_pow_mul_geometric_of_norm_lt_one k hnorm).comp_injective
    (fun a b h => Nat.add_right_cancel h : Function.Injective (fun n : ℕ => n+shift))
  have hsp : Summable (fun n : ℕ => ((n+shift : ℕ) : ℝ)^k * ρ^n) := by
    by_cases hρ : ρ = 0
    · subst ρ
      exact summable_of_ne_finset_zero (s := {0}) (by
        intro n hn
        have hn0 : n ≠ 0 := by simpa only [Finset.mem_singleton] using hn
        simp [hn0])
    · have h := hp.mul_right (ρ^shift)⁻¹
      simpa only [Function.comp_apply, pow_add, mul_assoc,
        mul_inv_cancel₀ (pow_ne_zero shift hρ), mul_one] using h
  apply Summable.of_norm_bounded (hsp.mul_left C)
  intro n
  simpa only [mul_assoc] using hb n

/-- The printed anchored fermion trace bound is itself dominated by a polynomial
    times rho^n; no COM dimension factor is used here. -/
theorem anchored_trace_majorant (n : ℕ) :
    Real.sqrt (2 * (n+2 : ℕ)) + (n+2 : ℕ) - 1 ≤ 3 * (n+3 : ℕ) := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hs : Real.sqrt (2 * (n+2 : ℕ)) ≤ (n+3 : ℕ) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · push_cast
      nlinarith [sq_nonneg (n : ℝ)]
  push_cast at hs ⊢
  linarith

/-- Exact index alignment for the printed anchored route: l=n+2, L=l+1,
    and the squared periodization factor (L+1)^6=(n+4)^6.
    C may depend on a fixed flux/particle sector. This does not pay errors by H. -/
theorem summable_anchored_periodized_blocks {V : Type*}
    [NormedAddCommGroup V] [CompleteSpace V] {blocks : ℕ → V}
    {C ρ : ℝ} (hC : 0 ≤ C) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hb : ∀ n, ‖blocks n‖ ≤ C * ((n+4 : ℕ) : ℝ)^6 *
      (Real.sqrt (2 * (n+2 : ℕ)) + (n+2 : ℕ) - 1) * ρ^(n+2)) :
    Summable blocks := by
  apply summable_polynomial_geometric_bound (C := C * 3 * ρ^2) 4 7 hρ0 hρ1
  intro n
  have ht : Real.sqrt (2 * (n+2 : ℕ)) + (n+2 : ℕ) - 1 ≤ 3 * (n+4 : ℕ) := by
    have h := anchored_trace_majorant n
    push_cast at h ⊢
    linarith
  calc
    ‖blocks n‖ ≤ C * ((n+4 : ℕ) : ℝ)^6 *
        (Real.sqrt (2 * (n+2 : ℕ)) + (n+2 : ℕ) - 1) * ρ^(n+2) := hb n
    _ ≤ C * ((n+4 : ℕ) : ℝ)^6 * (3 * (n+4 : ℕ)) * ρ^(n+2) := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hρ0 _)
      exact mul_le_mul_of_nonneg_left ht (mul_nonneg hC (by positivity))
    _ = C * 3 * ρ^2 * ((n+4 : ℕ) : ℝ)^7 * ρ^n := by
      rw [pow_add]
      ring

/-- One degree's Pauli estimate is integrated using *each* exact pair descendant
    energy, rather than counting particle pairs or using a many-body norm. -/
theorem integrated_descendant_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {pair : ℕ → X → ℝ} {d : X → ℝ} {z : ℕ} {Mz E : ℝ}
    (hp : ∀ p, Integrable (pair p) μ)
    (henergy : ∀ p, ∫ x, pair p x ∂μ = E)
    (hdmeas : AEStronglyMeasurable d μ)
    (hd0 : ∀ x, 0 ≤ d x)
    (hd : ∀ x, d x ≤ Mz * ∑ p ∈ Finset.range (z+1), pair p x) :
    Integrable d μ ∧ (∫ x, d x ∂μ) ≤ Mz * (z+1) * E := by
  have hsum : Integrable (fun x => ∑ p ∈ Finset.range (z+1), pair p x) μ :=
    integrable_finsetSum _ (fun p _ => hp p)
  have hdom := hsum.const_mul Mz
  have hdint : Integrable d μ := hdom.mono_nonneg hdmeas
    (Filter.Eventually.of_forall hd0) (Filter.Eventually.of_forall hd)
  constructor
  · exact hdint
  · calc
      (∫ x, d x ∂μ) ≤ ∫ x, Mz * ∑ p ∈ Finset.range (z+1), pair p x ∂μ :=
        integral_mono hdint hdom hd
      _ = Mz * (z+1) * E := by
        rw [integral_const_mul, integral_finsetSum _ (fun p _ => hp p)]
        simp only [henergy, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-- The local Pauli bound and the actual summable high-jet majorant justify
    exchanging the negative series with its cell integral and pay it by E.
    Physical instantiation uses d=||D_z psi||^2, pair=||B_p psi||^2,
    μ=dmu2 and E=Re<psi,H psi>; edgeWeight contains dmu3/dmu2. -/
theorem integrated_negative_tail {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {pair d : ℕ → X → ℝ} {M : ℕ → ℝ} {C E : ℝ}
    (hp : ∀ p, Integrable (pair p) μ)
    (henergy : ∀ p, ∫ x, pair p x ∂μ = E)
    (hM0 : ∀ z, 0 ≤ M z) (hM : ∀ z, M z ≤ C * (z+1))
    (hdmeas : ∀ m, AEStronglyMeasurable (d m) μ)
    (hd0 : ∀ m x, 0 ≤ d m x)
    (hd : ∀ m x, d m x ≤ M (degree m) *
      ∑ p ∈ Finset.range (degree m+1), pair p x) :
    Summable (fun m => ∫ x, ‖-edgeWeight m * d m x‖ ∂μ) ∧
      -(delta M * E) ≤ ∫ x, ∑' m, -edgeWeight m * d m x ∂μ := by
  have hdi (m : ℕ) := integrated_descendant_bound hp henergy (hdmeas m) (hd0 m) (hd m)
  have hfint (m : ℕ) : Integrable (fun x => -edgeWeight m * d m x) μ :=
    (hdi m).1.const_mul _
  have hnorm (m : ℕ) :
      (∫ x, ‖-edgeWeight m * d m x‖ ∂μ) = edgeWeight m * ∫ x, d m x ∂μ := by
    simp_rw [Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_nonneg (edgeWeight_nonneg m), abs_of_nonneg (hd0 m _)]
    exact integral_const_mul _ _
  have hbound (m : ℕ) : edgeWeight m * (∫ x, d m x ∂μ) ≤
      weight m * M (degree m) * E := by
    calc
      _ ≤ edgeWeight m * (M (degree m) * (degree m+1) * E) :=
        mul_le_mul_of_nonneg_left (hdi m).2 (edgeWeight_nonneg m)
      _ = weight m * M (degree m) * E := by
        rw [← edgeWeight_mul_degree]
        ring
  have hsf := negative_tail_energy_bound hM0 hM
    (fun m => mul_nonneg (edgeWeight_nonneg m) (integral_nonneg (hd0 m))) hbound
  have hsum : Summable (fun m => ∫ x, ‖-edgeWeight m * d m x‖ ∂μ) := by
    simpa only [hnorm] using hsf.1
  constructor
  · exact hsum
  · rw [← integral_tsum_of_summable_integral_norm hfint hsum]
    simpa only [integral_const_mul, integral_neg, neg_mul] using hsf.2

end TorusLean.Fermion.AnchoredThreeBody

#print axioms TorusLean.Fermion.AnchoredThreeBody.summable_polynomial_geometric_bound
#print axioms TorusLean.Fermion.AnchoredThreeBody.anchored_trace_majorant
#print axioms TorusLean.Fermion.AnchoredThreeBody.summable_anchored_periodized_blocks
#print axioms TorusLean.Fermion.AnchoredThreeBody.integrated_descendant_bound
#print axioms TorusLean.Fermion.AnchoredThreeBody.integrated_negative_tail
