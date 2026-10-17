/- Scalar negative-tail bridge. Physical torus instantiation remains explicit. -/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option autoImplicit false
noncomputable section

namespace TorusLean.Fermion.UniformTail
open scoped BigOperators
open Filter Topology

/-- Enumerates exactly the negative odd degrees `z >= 17`. -/
def degree (m : ℕ) : ℕ := 2 * (m + 8) + 1

/-- The paper's exact connected coefficient; no spectrum is assumed. -/
def q (z : ℕ) : ℝ := (3 * z - 1) * (-1/2 : ℝ)^z

/-- Includes `dmu3/dmu2 = 3/2` and the `z+1` pair descendants. -/
def weight (m : ℕ) : ℝ :=
  (9 * (m + 8 : ℕ)^2 + 12 * (m + 8 : ℕ) + 3 : ℝ) * (1/4 : ℝ)^(m+8)

/-- The coefficient of a squared annihilation amplitude, before counting descendants. -/
def edgeWeight (m : ℕ) : ℝ :=
  (3/2 : ℝ) * (3 * degree m - 1) * (1/2 : ℝ)^degree m

theorem degree_odd_ge (m : ℕ) : Odd (degree m) ∧ 17 ≤ degree m := by
  constructor
  · exact ⟨m+8, by simp [degree]⟩
  · simp [degree]; omega

theorem degree_exhausts {z : ℕ} (hz : Odd z) (h17 : 17 ≤ z) :
    ∃ m, degree m = z := by
  obtain ⟨k, hk⟩ := hz
  refine ⟨k-8, ?_⟩
  unfold degree
  omega

theorem degree_injective : Function.Injective degree := by
  intro a b h
  unfold degree at h
  omega

/-- Bijective reindexing of the full odd tail, with no duplicated degrees. -/
def oddTailEquiv : ℕ ≃ {z : ℕ // Odd z ∧ 17 ≤ z} :=
  Equiv.ofBijective (fun m => ⟨degree m, degree_odd_ge m⟩) ⟨
    fun a b h => degree_injective (congrArg Subtype.val h),
    fun z => by
      obtain ⟨m, hm⟩ := degree_exhausts z.property.1 z.property.2
      exact ⟨m, Subtype.ext hm⟩⟩

theorem q_degree (m : ℕ) :
    q (degree m) = -((3 * degree m - 1) * (1/2 : ℝ)^degree m) := by
  have hn : ((-1 : ℝ) ^ degree m) = -1 := (degree_odd_ge m).1.neg_one_pow
  rw [q, show (-1/2 : ℝ) = -1 * (1/2) by ring, mul_pow, hn]
  ring

theorem edgeWeight_eq_neg_q (m : ℕ) :
    edgeWeight m = -(3/2 : ℝ) * q (degree m) := by
  rw [q_degree]
  unfold edgeWeight
  ring

theorem weight_nonneg (m : ℕ) : 0 ≤ weight m := by
  unfold weight
  positivity

theorem weight_eq_physical_coefficient (m : ℕ) :
    weight m = (3/2 : ℝ) * (3 * degree m - 1) * (degree m + 1) *
      (1/2 : ℝ) ^ degree m := by
  simp only [weight, degree, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    pow_add, pow_mul]
  norm_num
  ring

theorem edgeWeight_nonneg (m : ℕ) : 0 ≤ edgeWeight m := by
  have hd : (17 : ℝ) ≤ degree m := by exact_mod_cast (degree_odd_ge m).2
  unfold edgeWeight
  apply mul_nonneg
  · nlinarith
  · positivity

theorem edgeWeight_mul_degree (m : ℕ) :
    edgeWeight m * (degree m + 1) = weight m := by
  rw [weight_eq_physical_coefficient]
  unfold edgeWeight
  ring

private theorem quarter_norm : ‖(1/4 : ℝ)‖ < 1 := by norm_num

theorem weight_hasSum : HasSum weight (61/4096 : ℝ) := by
  have h0 := hasSum_geometric_of_norm_lt_one quarter_norm
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one quarter_norm
  have h2 := hasSum_sq_mul_geometric_of_norm_lt_one quarter_norm
  have h := ((h2.mul_left 9).add (h1.mul_left 156)).add (h0.mul_left 675)
  have h' := h.mul_right ((1/4 : ℝ)^8)
  convert h' using 1
  · ext m
    simp only [weight, Nat.cast_add, Nat.cast_ofNat, pow_add]
    ring
  · norm_num

theorem weight_tsum : ∑' m, weight m = (61/4096 : ℝ) := weight_hasSum.tsum_eq

theorem weight_summable : Summable weight := weight_hasSum.summable

/-- The high-jet envelope introduces just one extra polynomial degree. -/
theorem weighted_degree_summable : Summable (fun m => weight m * (degree m + 1)) := by
  have hp (k : ℕ) : Summable (fun m : ℕ => ((m+8 : ℕ) : ℝ)^k * (1/4 : ℝ)^(m+8)) :=
    (summable_pow_mul_geometric_of_norm_lt_one k quarter_norm).comp_injective
      (fun a b h => Nat.add_right_cancel h)
  have h := (((hp 3).mul_left 18).add ((hp 2).mul_left 42)).add
    (((hp 1).mul_left 30).add ((hp 0).mul_left 6))
  convert h using 1
  ext m
  simp only [weight, degree, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    pow_zero, pow_one]
  ring

/-- No H or geometry is redefined: M is the actual high-jet squared-norm envelope.
    As with all real `tsum`, interpreting this as a convergent physical tail
    requires a summability proof, supplied below by `delta_summable`. -/
def delta (M : ℕ → ℝ) : ℝ := ∑' m, weight m * M (degree m)

/-- Exact reindexing of the totalized series over every odd z>=17.
    Its convergent-tail interpretation additionally uses `delta_summable`. -/
theorem physical_odd_tail_reindex (M : ℕ → ℝ) :
    (∑' z : {z : ℕ // Odd z ∧ 17 ≤ z},
      (3/2 : ℝ) * (3 * z.val - 1) * (z.val + 1) * (1/2 : ℝ)^z.val * M z.val) =
      delta M := by
  rw [← oddTailEquiv.tsum_eq]
  unfold delta
  apply tsum_congr
  intro m
  change (3/2 : ℝ) * (3 * degree m - 1) * (degree m + 1) *
    (1/2 : ℝ)^degree m * M (degree m) = weight m * M (degree m)
  rw [weight_eq_physical_coefficient]

theorem physical_odd_tail_tsum :
    (∑' z : {z : ℕ // Odd z ∧ 17 ≤ z},
      (3/2 : ℝ) * (3 * z.val - 1) * (z.val + 1) * (1/2 : ℝ)^z.val) =
      (61/4096 : ℝ) := by
  simpa only [mul_one, delta, weight_tsum] using physical_odd_tail_reindex (fun _ => 1)

theorem delta_summable {M : ℕ → ℝ} {C : ℝ}
    (hM0 : ∀ z, 0 ≤ M z) (hM : ∀ z, M z ≤ C * (z+1)) :
    Summable (fun m => weight m * M (degree m)) := by
  apply Summable.of_nonneg_of_le (fun m => mul_nonneg (weight_nonneg m) (hM0 _))
    (fun m => mul_le_mul_of_nonneg_left (hM _) (weight_nonneg m))
  simpa only [mul_left_comm, mul_assoc] using weighted_degree_summable.mul_left C

/-- Uses one bound C for the entire geometry/twist filter, not one C per sequence. -/
theorem delta_tendsto {G : Type*} {l : Filter G} {M : G → ℕ → ℝ} {C : ℝ}
    (hM : ∀ᶠ g in l, ∀ z, 0 ≤ M g z ∧ M g z ≤ C * (z+1))
    (hlim : ∀ z, Tendsto (fun g => M g z) l (𝓝 1)) :
    Tendsto (fun g => delta (M g)) l (𝓝 (61/4096 : ℝ)) := by
  have hs : Summable (fun m => C * (weight m * (degree m + 1))) :=
    weighted_degree_summable.mul_left C
  have h := tendsto_tsum_of_dominated_convergence hs
    (fun m => (hlim (degree m)).const_mul (weight m)) ?_
  · simpa only [mul_one, weight_tsum, delta] using h
  · filter_upwards [hM] with g hg m
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (weight_nonneg m) (hg _).1)]
    calc
      weight m * M g (degree m) ≤ weight m * (C * (degree m + 1)) :=
        mul_le_mul_of_nonneg_left (hg _).2 (weight_nonneg m)
      _ = C * (weight m * (degree m + 1)) := by ring

/-- Pointwise energy domination plus the proven majorant gives an H-relative tail.
    E must later be instantiated with the existing physical pair energy. -/
theorem negative_tail_energy_bound {M f : ℕ → ℝ} {C E : ℝ}
    (hM0 : ∀ z, 0 ≤ M z) (hM : ∀ z, M z ≤ C * (z+1))
    (hf0 : ∀ m, 0 ≤ f m)
    (hf : ∀ m, f m ≤ weight m * M (degree m) * E) :
    Summable f ∧ -(delta M * E) ≤ ∑' m, -f m := by
  have hs := (delta_summable hM0 hM).mul_right E
  have hsf := Summable.of_nonneg_of_le hf0 hf hs
  constructor
  · exact hsf
  · have hle := hsf.tsum_le_tsum hf hs
    rw [tsum_neg]
    rw [tsum_mul_right] at hle
    exact neg_le_neg hle

end TorusLean.Fermion.UniformTail
