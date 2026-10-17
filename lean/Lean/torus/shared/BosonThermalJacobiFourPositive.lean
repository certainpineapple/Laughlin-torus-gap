import torus.shared.BosonThermalJacobiPositive
import torus.shared.ThermalCoherentJacobiFourAmplitude

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonThermalJacobiFourPositive
open TorusLean.Shared.BosonThermalJacobiPositive
open TorusLean.Shared.ThermalCoherentJacobiFourWeights TorusLean.Shared.ThermalCoherentMoments
open scoped BigOperators

/-- The exact Jacobi heat series follows from positive diagonalization of
any genuine nonnegative relative forms. No a→0 exchange is asserted. -/
theorem four_jacobi_hasSum (a : ℝ) (ha : 0 < a) (Q : ℕ → ℝ)
    (hQ : ∀ d, 0 ≤ Q d) (S : ℝ)
    (hS : HasSum (fun j => thermalEigenvalue a j *
      ((1/2:ℝ) * ∑ d ∈ Finset.range (j+1), (fourSignedAmplitude (j-d) d)^2 * Q d)) S) :
    HasSum (fun d => (1/(1+2*a))^(d+1) * Q d) S := by
  let F : ℕ × ℕ → ℝ := fun p => fourCOMWeight a p.1 p.2 * Q p.1
  have hF (p : ℕ × ℕ) : 0 ≤ F p :=
    mul_nonneg (fourCOMWeight_nonneg a ha p.1 p.2) (hQ p.1)
  have he (j : ℕ) : (∑ p ∈ Finset.antidiagonal j, F p) =
      thermalEigenvalue a j * ((1/2:ℝ) *
        ∑ d ∈ Finset.range (j+1), (fourSignedAmplitude (j-d) d)^2 * Q d) := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hle : d ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
    dsimp [F]
    rw [fourCOMWeight_eq_amplitude_sq,Nat.sub_add_cancel hle]
    ring
  have hp : HasSum F S := hasSum_prod_of_nonnegative_antidiagonal F hF S
    (hS.congr_fun he)
  exact hp.prod_fiberwise fun d => (hasSum_fourCOMWeight a ha d).mul_right (Q d)


/-- Positive two-relative-mode transport after the actual finite spectator
rotation. All reordering is justified by nonnegative summability; no
unweighted limit or arbitrary operator trace is used. -/
theorem four_double_jacobi_hasSum (a : ℝ) (ha : 0<a) (Q : ℕ × ℕ → ℝ)
    (hQ : ∀ de, 0≤Q de) (S : ℝ)
    (hS : HasSum (fun dl : ℕ × ℕ => thermalEigenvalue a dl.1 * thermalEigenvalue a dl.2 *
      ((1/2:ℝ) * ∑ e ∈ Finset.range (dl.2+1),
        (fourSignedAmplitude (dl.2-e) e)^2 * Q (dl.1,e))) S) :
    HasSum (fun de : ℕ × ℕ => (1/(1+a))^(de.1+1) * (1/(1+2*a))^(de.2+1) * Q de) S := by
  let F : ℕ × ℕ → ℝ := fun dl => thermalEigenvalue a dl.1 * thermalEigenvalue a dl.2 *
    ((1/2:ℝ) * ∑ e ∈ Finset.range (dl.2+1),
      (fourSignedAmplitude (dl.2-e) e)^2 * Q (dl.1,e))
  let T : ℕ × ℕ → ℝ := fun de => (1/(1+a))^(de.1+1) * (1/(1+2*a))^(de.2+1) * Q de
  have hd (d : ℕ) : HasSum (fun e => T (d,e)) (∑' l, F (d,l)) := by
    have hs := (hS.summable.prod_factor d).hasSum
    have he (l : ℕ) : thermalEigenvalue a l *
        ((1/2:ℝ) * ∑ e ∈ Finset.range (l+1),
          (fourSignedAmplitude (l-e) e)^2 * (thermalEigenvalue a d * Q (d,e))) = F (d,l) := by
      dsimp [F]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      ring
    have hj := four_jacobi_hasSum a ha (fun e => thermalEigenvalue a d * Q (d,e))
      (fun e => mul_nonneg (thermalEigenvalue_pos a ha d).le (hQ (d,e)))
      (∑' l, F (d,l)) (hs.congr_fun he)
    apply hj.congr_fun
    intro e
    dsimp [T]
    simp only [thermalEigenvalue,one_div,inv_pow]
    ring
  have ho : HasSum (fun d => ∑' l, F (d,l)) S :=
    hS.prod_fiberwise fun d => (hS.summable.prod_factor d).hasSum
  have ht0 (de : ℕ × ℕ) : 0≤T de := by
    dsimp [T]
    exact mul_nonneg (mul_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (by positivity) _)) (hQ de)
  have ht : Summable T := (summable_prod_of_nonneg ht0).2 ⟨fun d => (hd d).summable,
    ho.summable.congr (fun d => (hd d).tsum_eq.symm)⟩
  have hv := ht.hasSum.prod_fiberwise hd
  exact hv.unique ho ▸ ht.hasSum

end TorusLean.Shared.BosonThermalJacobiFourPositive
