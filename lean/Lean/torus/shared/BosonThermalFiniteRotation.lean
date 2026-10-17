import torus.shared.BosonThermalJacobiPositive

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonThermalFiniteRotation
open TorusLean.Shared.BosonThermalJacobiPositive TorusLean.Shared.ThermalCoherentMoments
open scoped BigOperators

/-- Finite total-degree trace identities commute with equal positive heat
weights. Actual summability is established before the antidiagonal change. -/
theorem thermal_rotation_hasSum (a : ℝ) (ha : 0<a) (A B : ℕ × ℕ → ℝ)
    (hB : ∀ p, 0≤B p) (htrace : ∀ t,
      (∑ p ∈ Finset.antidiagonal t, A p) = ∑ p ∈ Finset.antidiagonal t, B p)
    (S : ℝ) (hS : HasSum (fun p : ℕ × ℕ => thermalEigenvalue a p.1 * thermalEigenvalue a p.2 * A p) S) :
    HasSum (fun p : ℕ × ℕ => thermalEigenvalue a p.1 * thermalEigenvalue a p.2 * B p) S := by
  have hw (t : ℕ) (p : ℕ × ℕ) (hp : p∈Finset.antidiagonal t) :
      thermalEigenvalue a p.1 * thermalEigenvalue a p.2 = ((1+a)^(t+2))⁻¹ := by
    have ht := Finset.mem_antidiagonal.mp hp
    simp only [thermalEigenvalue,← mul_inv,← pow_add]
    congr 2
    omega
  have hanti : HasSum (fun t => ∑ p ∈ Finset.antidiagonal t,
      thermalEigenvalue a p.1 * thermalEigenvalue a p.2 * A p) S := by
    have h := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.hasSum_iff.2 hS).sigma
      (fun t => hasSum_fintype (fun p : ↥(Finset.antidiagonal t) =>
        thermalEigenvalue a p.val.1 * thermalEigenvalue a p.val.2 * A p.val))
    apply h.congr_fun
    intro t
    exact (Finset.sum_coe_sort (Finset.antidiagonal t)
      (fun p : ℕ × ℕ => thermalEigenvalue a p.1 * thermalEigenvalue a p.2 * A p)).symm
  apply hasSum_prod_of_nonnegative_antidiagonal _
    (fun p => mul_nonneg (mul_nonneg (thermalEigenvalue_pos a ha p.1).le
      (thermalEigenvalue_pos a ha p.2).le) (hB p)) S
  apply hanti.congr_fun
  intro t
  calc
    _ = ((1+a)^(t+2))⁻¹ * ∑ p ∈ Finset.antidiagonal t, B p := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p hp => by rw [hw t p hp]
    _ = ((1+a)^(t+2))⁻¹ * ∑ p ∈ Finset.antidiagonal t, A p := by rw [htrace]
    _ = _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p hp => by rw [hw t p hp]

end TorusLean.Shared.BosonThermalFiniteRotation
