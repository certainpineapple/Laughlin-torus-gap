import torus.shared.ThermalCoherentJacobiWeights
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.Ring

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonThermalJacobiPositive
open TorusLean.Shared.ThermalCoherentJacobiWeights TorusLean.Shared.ThermalCoherentMoments
open scoped BigOperators

/-- Positive antidiagonal transport. The finite source sums have a genuine
HasSum input; this proves actual two-index summability before rearrangement. -/
theorem hasSum_prod_of_nonnegative_antidiagonal (F : ℕ × ℕ → ℝ)
    (hF : ∀ p, 0 ≤ F p) (S : ℝ)
    (hS : HasSum (fun j => ∑ p ∈ Finset.antidiagonal j, F p) S) :
    HasSum F S := by
  have hσ : Summable (fun x : Σ j : ℕ, ↥(Finset.antidiagonal j) => F x.2.val) := by
    apply (summable_sigma_of_nonneg (f := fun x : Σ j : ℕ, ↥(Finset.antidiagonal j) => F x.2.val)
      (fun x => hF x.2.val)).2
    constructor
    · intro j
      exact (hasSum_fintype _).summable
    · simpa only [tsum_fintype,Finset.sum_coe_sort] using hS.summable
  have hp : Summable F :=
    Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff.mp hσ
  have ha : HasSum (fun j => ∑ p ∈ Finset.antidiagonal j, F p) (∑' p, F p) := by
    have h := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.2 hp.hasSum).sigma
      (fun j => hasSum_fintype (fun p : ↥(Finset.antidiagonal j) => F p.val))
    simpa only [Finset.sum_coe_sort] using h
  exact ha.unique hS ▸ hp.hasSum

/-- The exact Jacobi heat series follows from positive diagonalization of
any genuine nonnegative relative forms. No a→0 exchange is asserted. -/
theorem thermal_jacobi_hasSum (a : ℝ) (ha : 0 < a) (Q : ℕ → ℝ)
    (hQ : ∀ d, 0 ≤ Q d) (S : ℝ)
    (hS : HasSum (fun j => thermalEigenvalue a j *
      ((2/3:ℝ) * ∑ d ∈ Finset.range (j+1), (jacobiAmplitude (j-d) d)^2 * Q d)) S) :
    HasSum (fun d => (2/(2+3*a))^(d+1) * Q d) S := by
  let F : ℕ × ℕ → ℝ := fun p => thermalJacobiWeight a p.1 p.2 * Q p.1
  have hF (p : ℕ × ℕ) : 0 ≤ F p :=
    mul_nonneg (thermalJacobiWeight_nonneg a ha p.1 p.2) (hQ p.1)
  have he (j : ℕ) : (∑ p ∈ Finset.antidiagonal j, F p) =
      thermalEigenvalue a j * ((2/3:ℝ) *
        ∑ d ∈ Finset.range (j+1), (jacobiAmplitude (j-d) d)^2 * Q d) := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hle : d ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
    dsimp [F]
    rw [thermalJacobiWeight_eq_amplitude_sq,Nat.sub_add_cancel hle]
    ring
  have hp : HasSum F S := hasSum_prod_of_nonnegative_antidiagonal F hF S
    (hS.congr_fun he)
  exact hp.prod_fiberwise fun d => (hasSum_thermalJacobiWeight a ha d).mul_right (Q d)

end TorusLean.Shared.BosonThermalJacobiPositive
