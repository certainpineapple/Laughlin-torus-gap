import TwoBodyLift

/-! The finite-output tensor extension of a scalar Gram bound in the true
factorial occupation metric. All occupation supports are the actual finite
polynomial supports. There is no particle-number or output-dimension factor. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRowMetric
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open scoped BigOperators ComplexConjugate
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Extending a genuine polynomial's coefficient sum by zeros changes no norm. -/
theorem normSq_supported (S : Finset (ι →₀ ℕ)) (f : Core ι ℂ) (hf : f.support ⊆ S) :
    q f = ∑ n ∈ S, (occupationMetricWeight (fun _ : ι => 1) n:ℝ)*‖f.coeff n‖^2 := by
  unfold q occupationMetricNormSq
  simp only [Complex.normSq_eq_norm_sq]
  apply Finset.sum_subset hf
  intro n hn hnf
  have hz : f.coeff n=0 := by simpa using hnf
  simp only [hz,norm_zero,zero_pow (by decide : 2≠0),mul_zero]

/-- A scalar matrix estimate acts on arbitrary finite-core output states.
The premise is a scalar estimate only, independent of these output states. -/
theorem occupation_matrix_bound {I : Type*} [Fintype I] (M : I → I → ℂ) (e : ℝ)
    (hM : ∀ c : I → ℂ, ‖∑ i, ∑ j, conj (c i)*M i j*c j‖ ≤ e*∑ i, ‖c i‖^2)
    (Y : I → Core ι ℂ) :
    ‖∑ i, ∑ j, M i j*ip (Y i) (Y j)‖ ≤ e*∑ i, q (Y i) := by
  classical
  let S := Finset.univ.biUnion (fun i => (Y i).support)
  have hY (i : I) : (Y i).support ⊆ S := by
    intro n hn
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hn⟩
  have he : (∑ i, ∑ j, M i j*ip (Y i) (Y j)) =
      ∑ n ∈ S, (occupationMetricWeight (fun _ : ι => 1) n:ℂ)*
        ∑ i, ∑ j, conj ((Y i).coeff n)*M i j*(Y j).coeff n := by
    simp_rw [inner_supported S _ _ (hY _),Finset.mul_sum]
    conv_lhs =>
      arg 2
      ext i
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mul_sum,Complex.star_def]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he]
  calc
    _ ≤ ∑ n ∈ S, ‖(occupationMetricWeight (fun _ : ι => 1) n:ℂ)*
        ∑ i, ∑ j, conj ((Y i).coeff n)*M i j*(Y j).coeff n‖ := norm_sum_le _ _
    _ = ∑ n ∈ S, (occupationMetricWeight (fun _ : ι => 1) n:ℝ)*
        ‖∑ i, ∑ j, conj ((Y i).coeff n)*M i j*(Y j).coeff n‖ := by
      simp only [norm_mul,Complex.norm_natCast]
    _ ≤ ∑ n ∈ S, (occupationMetricWeight (fun _ : ι => 1) n:ℝ)*
        (e*∑ i, ‖(Y i).coeff n‖^2) := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_left (hM (fun i => (Y i).coeff n)) (Nat.cast_nonneg _)
    _ = e*∑ n ∈ S, ∑ i, (occupationMetricWeight (fun _ : ι => 1) n:ℝ)*‖(Y i).coeff n‖^2 := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = e*∑ i, ∑ n ∈ S, (occupationMetricWeight (fun _ : ι => 1) n:ℝ)*‖(Y i).coeff n‖^2 := by
      rw [Finset.sum_comm]
    _ = e*∑ i, q (Y i) := by
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact (normSq_supported S _ (hY i)).symm

/-- Sharp finite coefficient Cauchy--Schwarz in the factorial norm. -/
theorem occupation_sum_cauchy {J : Type*} (s : Finset J)
    (c : J → ℝ) (X : J → Core ι ℂ) :
    q (∑ a ∈ s, (c a:ℂ) • X a) ≤ (∑ a ∈ s, (c a)^2)*∑ a ∈ s, q (X a) := by
  classical
  let S := s.biUnion (fun a => (X a).support)
  have hX (a : J) (ha : a∈s) : (X a).support ⊆ S := by
    intro n hn
    exact Finset.mem_biUnion.mpr ⟨a,ha,hn⟩
  have hs : (∑ a ∈ s, (c a:ℂ) • X a).support ⊆ S := by
    intro n hn
    obtain ⟨a,ha,hna⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hn)
    exact hX a ha (MvPolynomial.support_smul hna)
  rw [normSq_supported S _ hs]
  have hsum : (∑ a ∈ s, q (X a)) = ∑ a ∈ s, ∑ n ∈ S,
      (occupationMetricWeight (fun _ : ι => 1) n:ℝ)*‖(X a).coeff n‖^2 := by
    apply Finset.sum_congr rfl
    intro a ha
    exact normSq_supported S _ (hX a ha)
  rw [hsum]
  rw [Finset.sum_comm (f := fun a n =>
    (occupationMetricWeight (fun _ : ι => 1) n:ℝ)*‖(X a).coeff n‖^2),Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  simp only [MvPolynomial.coeff_sum,MvPolynomial.coeff_smul,smul_eq_mul]
  have ht : ‖∑ a ∈ s, (c a:ℂ)*(X a).coeff n‖ ≤ ∑ a ∈ s, |c a| *‖(X a).coeff n‖ := by
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs] using
      norm_sum_le s (fun a => (c a:ℂ)*(X a).coeff n)
  have hc := Finset.sum_mul_sq_le_sq_mul_sq s (fun a => |c a|) (fun a => ‖(X a).coeff n‖)
  simp only [sq_abs] at hc
  have hb := (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans hc
  calc
    _ ≤ (occupationMetricWeight (fun _ : ι => 1) n:ℝ)*
        ((∑ a ∈ s, (c a)^2)*∑ a ∈ s, ‖(X a).coeff n‖^2) :=
      mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- Grouping by the creator index counts every original entry exactly once. -/
theorem sum_grouped {I J V : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [AddCommMonoid V] (r : J → I) (v : J → V) :
    (∑ i, ∑ a ∈ Finset.univ.filter (fun a => r a=i), v a) = ∑ a, v a := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  exact Finset.sum_ite_eq_of_mem Finset.univ (r a) (fun _ => v a) (Finset.mem_univ _)

/-- The sharp coefficient budget survives grouping, with no creator-index
cardinality factor and no particle-number estimate. -/
theorem grouped_output_norm_bound {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (r : J → I) (c : J → ℝ) (X : J → Core ι ℂ) :
    (∑ i, q (∑ a ∈ Finset.univ.filter (fun a => r a=i), (c a:ℂ) • X a)) ≤
      (∑ a, (c a)^2)*∑ a, q (X a) := by
  classical
  calc
    _ ≤ ∑ i, (∑ a, (c a)^2)*∑ a ∈ Finset.univ.filter (fun a => r a=i), q (X a) := by
      apply Finset.sum_le_sum
      intro i hi
      apply (occupation_sum_cauchy _ c X).trans
      apply mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg (fun a _ => occupationMetricNormSq_nonneg _ _))
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun a _ _ => sq_nonneg (c a))
    _ = _ := by rw [← Finset.mul_sum,sum_grouped]

end TorusLean.Shared.ThermalCoherentBosonRowMetric
