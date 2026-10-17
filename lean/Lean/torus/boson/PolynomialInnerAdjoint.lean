import torus.boson.FiniteOccupationCCR
import torus.boson.WeightedOccupationMetric
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Basic.Complex.BigOperators

/-!
# Sesquilinear occupation inner product and polynomial adjoints

The common domain is the finite polynomial core, with unrestricted natural
occupations. The first argument is conjugate-linear. Positive mode scales
give a positive-definite inner product; zero scales are allowed only in the
sesquilinear identities, where the form may be degenerate.

For scale one, multiplication by `X i` and formal `pderiv i` are mutually
adjoint on this domain. General scales retain the exact scale factor.
The physical torus LLL basis and its unitary identification with this core
are still pending. No physical Hamiltonian or infinite-Fock operator is
defined here.
-/

namespace TorusLean.Boson

open scoped BigOperators ComplexConjugate

variable {ι : Type*} [Fintype ι]

noncomputable section

/-- Actual finite-support sesquilinear occupation form, conjugate-linear first. -/
def occupationInner (scale : ι → ℕ) (f g : Core ι ℂ) : ℂ :=
  f.coeff.sum fun n c => (occupationMetricWeight scale n : ℂ) * star c * g.coeff n

theorem occupationInner_monomial_left (scale : ι → ℕ) (n : ι →₀ ℕ)
    (c : ℂ) (g : Core ι ℂ) :
    occupationInner scale (MvPolynomial.monomial n c) g =
      (occupationMetricWeight scale n : ℂ) * star c * g.coeff n := by
  simp [occupationInner]

theorem occupationInner_zero_left (scale : ι → ℕ) (g : Core ι ℂ) :
    occupationInner scale 0 g = 0 := by
  simp [occupationInner]

theorem occupationInner_zero_right (scale : ι → ℕ) (f : Core ι ℂ) :
    occupationInner scale f 0 = 0 := by
  simp [occupationInner]

theorem occupationInner_add_left (scale : ι → ℕ) (f g h : Core ι ℂ) :
    occupationInner scale (f + g) h =
      occupationInner scale f h + occupationInner scale g h := by
  unfold occupationInner
  rw [AddMonoidAlgebra.coeff_add]
  apply Finsupp.sum_add_index'
  · intro n
    simp
  · intro n c d
    simp [star_add, mul_add, add_mul]

theorem occupationInner_add_right (scale : ι → ℕ) (f g h : Core ι ℂ) :
    occupationInner scale f (g + h) =
      occupationInner scale f g + occupationInner scale f h := by
  simp [occupationInner, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add]

theorem occupationInner_smul_left (scale : ι → ℕ) (c : ℂ) (f g : Core ι ℂ) :
    occupationInner scale (c • f) g = star c * occupationInner scale f g := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial n d =>
    simp [MvPolynomial.smul_monomial, occupationInner_monomial_left,
      smul_eq_mul, star_mul, mul_assoc, mul_comm, mul_left_comm]
  | add f h hf hh =>
    simp [smul_add, occupationInner_add_left, hf, hh, mul_add]

theorem occupationInner_smul_right (scale : ι → ℕ) (c : ℂ) (f g : Core ι ℂ) :
    occupationInner scale f (c • g) = c * occupationInner scale f g := by
  unfold occupationInner
  simp only [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem occupationInner_conj_symm (scale : ι → ℕ) (f g : Core ι ℂ) :
    star (occupationInner scale f g) = occupationInner scale g f := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f h hf hh =>
    simp [occupationInner_add_left, occupationInner_add_right, star_add, hf, hh]
  | monomial n c =>
    induction g using MvPolynomial.induction_on' with
    | add g h hg hh =>
      simp [occupationInner_add_left, occupationInner_add_right, star_add, hg, hh]
    | monomial m d =>
      by_cases h : n = m
      · subst m
        simp [occupationInner_monomial_left, MvPolynomial.coeff_monomial,
          star_mul, mul_assoc, mul_comm, mul_left_comm]
      · simp [occupationInner_monomial_left, MvPolynomial.coeff_monomial, h, Ne.symm h]

theorem occupationInner_self (scale : ι → ℕ) (f : Core ι ℂ) :
    occupationInner scale f f = (occupationMetricNormSq scale f : ℂ) := by
  classical
  unfold occupationInner occupationMetricNormSq
  simp only [Finsupp.sum, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_natCast, Complex.normSq_eq_conj_mul_self, Complex.star_def, mul_assoc,
    MvPolynomial.finsupp_support_eq_support]

theorem occupationInner_self_re (scale : ι → ℕ) (f : Core ι ℂ) :
    (occupationInner scale f f).re = occupationMetricNormSq scale f := by
  rw [occupationInner_self]
  simp

theorem occupationInner_self_nonneg (scale : ι → ℕ) (f : Core ι ℂ) :
    0 ≤ (occupationInner scale f f).re := by
  rw [occupationInner_self_re]
  exact occupationMetricNormSq_nonneg scale f

theorem occupationMetricNormSq_pos (scale : ι → ℕ)
    (hscale : ∀ i, 0 < scale i) (f : Core ι ℂ) (hf : f ≠ 0) :
    0 < occupationMetricNormSq scale f := by
  classical
  unfold occupationMetricNormSq
  apply Finset.sum_pos
  · intro n hn
    exact mul_pos (Nat.cast_pos.mpr (occupationMetricWeight_pos scale hscale n))
      (Complex.normSq_pos.mpr (MvPolynomial.mem_support_iff.mp hn))
  · exact MvPolynomial.support_nonempty.mpr hf

theorem occupationInner_self_eq_zero_iff (scale : ι → ℕ)
    (hscale : ∀ i, 0 < scale i) (f : Core ι ℂ) :
    occupationInner scale f f = 0 ↔ f = 0 := by
  constructor
  · intro h
    by_contra hf
    have hz : occupationMetricNormSq scale f = 0 := by
      have hr := congrArg Complex.re h
      simpa only [occupationInner_self_re, Complex.zero_re] using hr
    exact (ne_of_gt (occupationMetricNormSq_pos scale hscale f hf)) hz
  · intro h
    subst f
    exact occupationInner_zero_left scale 0

/-- Exact polynomial adjoint identity with the general coordinate scale. -/
theorem create_adjoint_scaled (scale : ι → ℕ) (i : ι) (f g : Core ι ℂ) :
    occupationInner scale (create i f) g =
      (scale i : ℂ) * occupationInner scale f (annihilate i g) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | add f h hf hh =>
    simp [map_add, occupationInner_add_left, hf, hh, mul_add]
  | monomial n c =>
    have hc : create i (MvPolynomial.monomial n c) =
        MvPolynomial.monomial (n + Finsupp.single i 1) c := by
      simp [create, MvPolynomial.X, MvPolynomial.monomial_mul_monomial, add_comm]
    rw [hc, occupationInner_monomial_left, occupationInner_monomial_left]
    have hcoef : (annihilate i g).coeff n =
        g.coeff (n + Finsupp.single i 1) * ((n i : ℂ) + 1) := by
      simpa [annihilate, Nat.cast_add, Nat.cast_one] using (MvPolynomial.coeff_pderiv g n)
    rw [hcoef, occupationMetricWeight_add_single]
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

theorem annihilate_adjoint_scaled (scale : ι → ℕ) (i : ι) (f g : Core ι ℂ) :
    (scale i : ℂ) * occupationInner scale (annihilate i f) g =
      occupationInner scale f (create i g) := by
  have h := congrArg star (create_adjoint_scaled scale i g f)
  simpa only [occupationInner_conj_symm, star_mul, star_natCast, mul_comm] using h.symm

/-- General scale gives `pderiv_i* = X_i / scale_i`, with nonzero scale explicit. -/
theorem annihilate_adjoint_div (scale : ι → ℕ) (i : ι) (hscale : scale i ≠ 0)
    (f g : Core ι ℂ) :
    occupationInner scale (annihilate i f) g =
      occupationInner scale f (create i g) / (scale i : ℂ) := by
  have hs : (scale i : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hscale
  apply (eq_div_iff hs).mpr
  simpa only [mul_comm] using annihilate_adjoint_scaled scale i f g

theorem create_adjoint_canonical (i : ι) (f g : Core ι ℂ) :
    occupationInner (fun _ => 1) (create i f) g =
      occupationInner (fun _ => 1) f (annihilate i g) := by
  simpa using create_adjoint_scaled (fun _ => 1) i f g

theorem annihilate_adjoint_canonical (i : ι) (f g : Core ι ℂ) :
    occupationInner (fun _ => 1) (annihilate i f) g =
      occupationInner (fun _ => 1) f (create i g) := by
  simpa using annihilate_adjoint_scaled (fun _ => 1) i f g

#print axioms occupationInner_monomial_left
#print axioms occupationInner_zero_left
#print axioms occupationInner_zero_right
#print axioms occupationInner_add_left
#print axioms occupationInner_add_right
#print axioms occupationInner_smul_left
#print axioms occupationInner_smul_right
#print axioms occupationInner_conj_symm
#print axioms occupationInner_self
#print axioms occupationInner_self_re
#print axioms occupationInner_self_nonneg
#print axioms occupationMetricNormSq_pos
#print axioms occupationInner_self_eq_zero_iff
#print axioms create_adjoint_scaled
#print axioms annihilate_adjoint_scaled
#print axioms annihilate_adjoint_div
#print axioms create_adjoint_canonical
#print axioms annihilate_adjoint_canonical

end

end TorusLean.Boson
