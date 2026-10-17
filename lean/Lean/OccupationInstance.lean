import torus.boson.FiniteOccupationCCR
import torus.boson.OccupationControl
import torus.boson.WeightedOccupationMetric
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Data.Finsupp.Order
import Mathlib.Analysis.Real.Sqrt
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Concrete occupation control using the coordinator's actual Core, annihilator,
pair map and fixed factorial occupation metric. The final paper-mode instances
have no arbitrary external weights or contact-budget hypotheses. They are
finite-mode polynomial results; no identification with physical torus LLL or
its coherent/contact Hamiltonian is asserted.
-/

set_option autoImplicit false
namespace TorusLean.BosonBridge.OccupationInstance
noncomputable section
open scoped BigOperators
open MvPolynomial TorusLean.Boson
variable {ι : Type*} [Fintype ι]

abbrev Occ (ι : Type*) := ι →₀ ℕ

def occupationMoment (scale : ι → ℕ) (f : Core ι ℂ) (i : ι) (b : ℕ → ℝ) : ℝ :=
  ∑' n : Occ ι, (occupationMetricWeight scale n : ℝ) *
    Complex.normSq (f.coeff n) * b (n i)

/-- Normalized pair in a unit-scale basis direction. The final paper zero
mode has scale 0!=1. This is the existing pair map, not a replacement H. -/
def normalizedUnitPair (i : ι) (f : Core ι ℂ) : Core ι ℂ :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (pairAnnihilate i i f)

theorem occupationMoment_summable (scale : ι → ℕ) (f : Core ι ℂ) (i : ι) (b : ℕ → ℝ) :
    Summable (fun n : Occ ι => (occupationMetricWeight scale n : ℝ) *
      Complex.normSq (f.coeff n) * b (n i)) := by
  classical
  apply summable_of_ne_finset_zero (s := f.support)
  intro n hn
  simp [MvPolynomial.notMem_support_iff.mp hn]

theorem occupationMoment_eq_finite (scale : ι → ℕ) (f : Core ι ℂ) (i : ι) (b : ℕ → ℝ) :
    occupationMoment scale f i b =
      ∑ n ∈ f.support, (occupationMetricWeight scale n : ℝ) *
        Complex.normSq (f.coeff n) * b (n i) := by
  classical
  apply tsum_eq_sum
  intro n hn
  simp [MvPolynomial.notMem_support_iff.mp hn]

theorem metricNormSq_eq_moment (scale : ι → ℕ) (f : Core ι ℂ) (i : ι) :
    occupationMetricNormSq scale f = occupationMoment scale f i (fun _ => 1) := by
  rw [occupationMoment_eq_finite]
  simp [occupationMetricNormSq]

private theorem gram_shift_one (scale : ι → ℕ) (i : ι) (hi : scale i = 1) (n : Occ ι) :
    (occupationMetricWeight scale (n + Finsupp.single i 1) : ℝ) =
      ((n i : ℝ) + 1) * (occupationMetricWeight scale n : ℝ) := by
  rw [occupationMetricWeight_add_single, hi]
  push_cast
  ring

private theorem gram_shift_two (scale : ι → ℕ) (i : ι) (hi : scale i = 1) (n : Occ ι) :
    (occupationMetricWeight scale (n + Finsupp.single i 2) : ℝ) =
      ((n i : ℝ) + 2) * ((n i : ℝ) + 1) * (occupationMetricWeight scale n : ℝ) := by
  have hs : n + Finsupp.single i 2 = (n + Finsupp.single i 1) + Finsupp.single i 1 := by
    rw [add_assoc, ← Finsupp.single_add]
  rw [hs, gram_shift_one scale i hi, gram_shift_one scale i hi]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.cast_add, Nat.cast_one]
  ring

private theorem shift_injective (i : ι) (k : ℕ) :
    Function.Injective (fun n : Occ ι => n + Finsupp.single i k) := by
  intro n m h
  exact add_right_cancel h

private theorem shift_preimage (i : ι) (n : Occ ι) (k : ℕ) (hk : k ≤ n i) :
    ∃ m : Occ ι, m + Finsupp.single i k = n := by
  refine ⟨n - Finsupp.single i k, ?_⟩
  exact tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hk)

/-- Actual annihilation form equals the occupation moment in a unit-scale
mode. There is no assumed physical adjoint/norm identity in the input. -/
theorem unit_annihilation_form (scale : ι → ℕ) (i : ι) (hi : scale i = 1) (f : Core ι ℂ) :
    occupationMetricNormSq scale (annihilate i f) =
      occupationMoment scale f i (fun n => (n : ℝ)) := by
  change occupationMetricNormSq scale (pderiv i f) = _
  let g : Occ ι → ℝ := fun n => (occupationMetricWeight scale n : ℝ) *
    Complex.normSq (f.coeff n) * (n i : ℝ)
  have hrange : Function.support g ⊆ Set.range (fun n : Occ ι => n + Finsupp.single i 1) := by
    intro n hn
    change g n ≠ 0 at hn
    have hni : n i ≠ 0 := by
      intro h0
      apply hn
      simp [g, h0]
    exact shift_preimage i n 1 (Nat.one_le_iff_ne_zero.mpr hni)
  have hterms : (fun n : Occ ι => (occupationMetricWeight scale n : ℝ) *
      Complex.normSq ((pderiv i f).coeff n) * (1 : ℝ)) =
      (fun n => g (n + Finsupp.single i 1)) := by
    funext n
    rw [MvPolynomial.coeff_pderiv]
    have hcast : (n i : ℂ) + 1 = ((n i + 1 : ℕ) : ℂ) := by simp
    rw [hcast, Complex.normSq_mul, Complex.normSq_natCast]
    dsimp [g]
    rw [gram_shift_one scale i hi]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.cast_add, Nat.cast_one]
    ring
  rw [metricNormSq_eq_moment scale (pderiv i f) i]
  unfold occupationMoment
  rw [hterms]
  exact (shift_injective i 1).tsum_eq hrange

/-- Actual two-removal form before its normalized pair factor. -/
theorem unit_second_annihilation_form (scale : ι → ℕ) (i : ι) (hi : scale i = 1) (f : Core ι ℂ) :
    occupationMetricNormSq scale (pairAnnihilate i i f) =
      occupationMoment scale f i (fun n => (n : ℝ) * ((n : ℝ) - 1)) := by
  change occupationMetricNormSq scale (pderiv i (pderiv i f)) = _
  let g : Occ ι → ℝ := fun n => (occupationMetricWeight scale n : ℝ) *
    Complex.normSq (f.coeff n) * ((n i : ℝ) * ((n i : ℝ) - 1))
  have hrange : Function.support g ⊆ Set.range (fun n : Occ ι => n + Finsupp.single i 2) := by
    intro n hn
    change g n ≠ 0 at hn
    have hni : 2 ≤ n i := by
      by_contra h2
      have hcases : n i = 0 ∨ n i = 1 := by omega
      rcases hcases with h0 | h1
      · apply hn; simp [g, h0]
      · apply hn; simp [g, h1]
    exact shift_preimage i n 2 hni
  have hterms : (fun n : Occ ι => (occupationMetricWeight scale n : ℝ) *
      Complex.normSq ((pderiv i (pderiv i f)).coeff n) * (1 : ℝ)) =
      (fun n => g (n + Finsupp.single i 2)) := by
    funext n
    rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv]
    have hs : (n + Finsupp.single i 1) + Finsupp.single i 1 = n + Finsupp.single i 2 := by
      rw [add_assoc, ← Finsupp.single_add]
    rw [hs]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    have hcast1 : (n i : ℂ) + 1 = ((n i + 1 : ℕ) : ℂ) := by simp
    have hcast2 : ((n i + 1 : ℕ) : ℂ) + 1 = ((n i + 2 : ℕ) : ℂ) := by push_cast; ring
    rw [hcast1, hcast2, Complex.normSq_mul, Complex.normSq_mul,
      Complex.normSq_natCast, Complex.normSq_natCast]
    dsimp [g]
    rw [gram_shift_two scale i hi]
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.cast_add,
      Nat.cast_one, Nat.cast_ofNat]
    ring
  rw [metricNormSq_eq_moment scale (pderiv i (pderiv i f)) i]
  unfold occupationMoment
  rw [hterms]
  exact (shift_injective i 2).tsum_eq hrange

theorem metricNormSq_smul (scale : ι → ℕ) (c : ℂ) (f : Core ι ℂ) (i : ι) :
    occupationMetricNormSq scale (c • f) = Complex.normSq c * occupationMetricNormSq scale f := by
  rw [metricNormSq_eq_moment scale (c • f) i, metricNormSq_eq_moment scale f i]
  unfold occupationMoment
  simp only [MvPolynomial.coeff_smul, smul_eq_mul, Complex.normSq_mul]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

theorem normalizedUnitPair_form (scale : ι → ℕ) (i : ι) (hi : scale i = 1) (f : Core ι ℂ) :
    occupationMetricNormSq scale (normalizedUnitPair i f) =
      occupationMoment scale f i pairOccupation := by
  have hs : Complex.normSq (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = 1 / 2 := by
    rw [Complex.normSq_inv, Complex.normSq_ofReal,
      Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [normalizedUnitPair, metricNormSq_smul scale _ _ i, hs,
    unit_second_annihilation_form scale i hi]
  unfold occupationMoment pairOccupation
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

/-- Concrete same-mode occupation domination in the existing factorial
metric; the only general-mode input is its one-particle normalization. -/
theorem unit_mode_occupation_control (scale : ι → ℕ) (i : ι) (hi : scale i = 1) (f : Core ι ℂ) :
    occupationMetricNormSq scale (annihilate i f) ≤
      occupationMetricNormSq scale (normalizedUnitPair i f) + occupationMetricNormSq scale f := by
  classical
  rw [unit_annihilation_form scale i hi, normalizedUnitPair_form scale i hi,
    metricNormSq_eq_moment scale f i, occupationMoment_eq_finite,
    occupationMoment_eq_finite, occupationMoment_eq_finite]
  simpa only [mul_one] using finite_occupation_le_pair_plus_mass f.support (fun n => n i)
    (fun n => (occupationMetricWeight scale n : ℝ) * Complex.normSq (f.coeff n))
    (fun n _ => mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _))

/-- K is a finite coordinate mode cap, not the torus flux or particle number. -/
def paperScales (K : ℕ) (j : Fin (K + 1)) : ℕ := j.val.factorial

/-- No external weights, Hamiltonian budget or N-dependent constant. -/
theorem paper_zero_mode_occupation_control (K : ℕ) (f : Core (Fin (K + 1)) ℂ) :
    occupationMetricNormSq (paperScales K) (annihilate 0 f) ≤
      occupationMetricNormSq (paperScales K) (normalizedUnitPair 0 f) +
        occupationMetricNormSq (paperScales K) f :=
  unit_mode_occupation_control (paperScales K) 0 (by simp [paperScales]) f

/-- The actual pair-output instance is a three-removal form paid by the
four-removal form and pair-output mass, with coefficient one for every K,N. -/
theorem paper_zero_mode_pair_output_control (K : ℕ) (f : Core (Fin (K + 1)) ℂ) :
    occupationMetricNormSq (paperScales K) (annihilate 0 (normalizedUnitPair 0 f)) ≤
      occupationMetricNormSq (paperScales K) (normalizedUnitPair 0 (normalizedUnitPair 0 f)) +
        occupationMetricNormSq (paperScales K) (normalizedUnitPair 0 f) :=
  paper_zero_mode_occupation_control K (normalizedUnitPair 0 f)

/-- The genuine polynomial annihilator lowers the actual total particle
degree by one. Input is N+1, avoiding any truncated Nat subtraction. -/
theorem annihilate_sector (N : ℕ) (i : ι) (f : Core ι ℂ)
    (hf : f.IsHomogeneous (N + 1)) : (annihilate i f).IsHomogeneous N := by
  intro n hn
  change ((pderiv i f).coeff n ≠ 0) at hn
  have hc : f.coeff (n + Finsupp.single i 1) ≠ 0 := by
    intro h0
    apply hn
    rw [MvPolynomial.coeff_pderiv, h0, zero_mul]
  have hd := hf hc
  simp only [map_add, Finsupp.weight_single, Pi.one_apply, one_smul] at hd
  change Finsupp.weight (1 : ι → ℕ) n = N
  omega

/-- The existing normalized pair map takes the N+2 homogeneous sector to N. -/
theorem normalizedUnitPair_sector (N : ℕ) (i : ι) (f : Core ι ℂ)
    (hf : f.IsHomogeneous (N + 2)) : (normalizedUnitPair i f).IsHomogeneous N := by
  have h1 : (annihilate i f).IsHomogeneous (N + 1) :=
    annihilate_sector (N + 1) i f (by simpa [Nat.add_assoc] using hf)
  have h2 := annihilate_sector N i (annihilate i f) h1
  intro n hn
  have hc : (annihilate i (annihilate i f)).coeff n ≠ 0 := by
    intro h0
    apply hn
    simp only [normalizedUnitPair, pairAnnihilate, LinearMap.comp_apply,
      MvPolynomial.coeff_smul, h0, smul_zero]
  exact h2 hc

/-- Fully scoped paper-mode instance: input N+4, pair output N+2, spectator
output N+1, second pair output N. The same coefficient one holds for all N. -/
theorem paper_pair_output_sector_control (K N : ℕ) (f : Core (Fin (K + 1)) ℂ)
    (hf : f.IsHomogeneous (N + 4)) :
    (annihilate 0 (normalizedUnitPair 0 f)).IsHomogeneous (N + 1) ∧
    (normalizedUnitPair 0 (normalizedUnitPair 0 f)).IsHomogeneous N ∧
    occupationMetricNormSq (paperScales K) (annihilate 0 (normalizedUnitPair 0 f)) ≤
      occupationMetricNormSq (paperScales K) (normalizedUnitPair 0 (normalizedUnitPair 0 f)) +
        occupationMetricNormSq (paperScales K) (normalizedUnitPair 0 f) := by
  have hp : (normalizedUnitPair (0 : Fin (K + 1)) f).IsHomogeneous (N + 2) :=
    normalizedUnitPair_sector (N + 2) 0 f (by simpa [Nat.add_assoc] using hf)
  refine ⟨?_, normalizedUnitPair_sector N 0 _ hp, paper_zero_mode_pair_output_control K f⟩
  exact annihilate_sector (N + 1) 0 _ (by simpa [Nat.add_assoc] using hp)

end
end TorusLean.BosonBridge.OccupationInstance
