import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith

/-!
Sector-sum form domains for bounded blocks over any RCLike scalar field.
This includes complex Sym^N(LLL) once the physical model and its operators
are defined. This file proves summability, uniform form
transfer and graph approximation; it does not assert a self-adjoint physical
Fock operator or prove the sector gap. All operators are indexed by one
fixed geometry/flux/twist. The index N varies only particle number.
-/

set_option autoImplicit false

namespace TorusLean.BosonBridge
noncomputable section
open scoped BigOperators
open Filter

variable {𝕜 : Type*} [RCLike 𝕜] {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace 𝕜 (E n)]

/-- The Hilbert-direct-sum membership condition at the sector coordinate level. -/
def InFockSpace (x : ∀ n, E n) : Prop := Summable (fun n => ‖x n‖ ^ 2)

/-- Coordinate graph condition for arbitrary bounded blocks. It becomes
D(H) after realizing the closed direct-sum operator. Its norm-square form
is associated with H*H; an H² interpretation additionally requires physical
self-adjointness. D(H²) is a separate stronger domain, not imposed here. -/
def InGraphDomain (H : ∀ n, E n →L[𝕜] E n) (x : ∀ n, E n) : Prop :=
  InFockSpace x ∧ Summable (fun n => ‖H n (x n)‖ ^ 2)

def sectorEnergy (H : ∀ n, E n →L[𝕜] E n) (x : ∀ n, E n) (n : ℕ) : ℝ :=
  RCLike.re (inner (𝕜 := 𝕜) (x n) (H n (x n)))

def hamiltonianForm (H : ∀ n, E n →L[𝕜] E n) (x : ∀ n, E n) : ℝ :=
  ∑' n, sectorEnergy H x n

/-- Historical API name for the norm-square sum, not an identification
with the quadratic form of H² for arbitrary H. -/
def hamiltonianSquareForm (H : ∀ n, E n →L[𝕜] E n) (x : ∀ n, E n) : ℝ :=
  ∑' n, ‖H n (x n)‖ ^ 2

def graphMass (H : ∀ n, E n →L[𝕜] E n) (x : ∀ n, E n) (n : ℕ) : ℝ :=
  ‖x n‖ ^ 2 + ‖H n (x n)‖ ^ 2

/-- Cauchy--Schwarz plus Young's inequality controls the absolute sector
energy using the two defining square sums. No uniform block norm is used. -/
theorem sectorEnergy_abs_le_graphMass (H : ∀ n, E n →L[𝕜] E n)
    (x : ∀ n, E n) (n : ℕ) :
    |sectorEnergy H x n| ≤ (1 / 2 : ℝ) * graphMass H x n := by
  have hcs := (RCLike.abs_re_le_norm (inner (𝕜 := 𝕜) (x n) (H n (x n)))).trans
    (norm_inner_le_norm (𝕜 := 𝕜) (x n) (H n (x n)))
  have hy := sq_nonneg (‖x n‖ - ‖H n (x n)‖)
  dsimp [sectorEnergy, graphMass]
  nlinarith

theorem graphMass_summable (H : ∀ n, E n →L[𝕜] E n)
    (x : ∀ n, E n) (hx : InGraphDomain H x) : Summable (graphMass H x) :=
  hx.1.add hx.2

/-- Absolute energy summability is a conclusion, not an extra domain input. -/
theorem sectorEnergy_abs_summable (H : ∀ n, E n →L[𝕜] E n)
    (x : ∀ n, E n) (hx : InGraphDomain H x) :
    Summable (fun n => |sectorEnergy H x n|) := by
  exact ((graphMass_summable H x hx).mul_left (1 / 2 : ℝ)).of_nonneg_of_le
    (fun _ => abs_nonneg _) (sectorEnergy_abs_le_graphMass H x)

theorem sectorEnergy_summable (H : ∀ n, E n →L[𝕜] E n)
    (x : ∀ n, E n) (hx : InGraphDomain H x) : Summable (sectorEnergy H x) :=
  (sectorEnergy_abs_summable H x hx).of_abs

/-- A single sector-independent coefficient extends to the norm-square
graph condition. Neither self-adjointness nor 0<γ is assumed.
The uniform sector estimate is explicit and still needs a physical proof.
This theorem proves no torus threshold, spectral calculus or kernel dimension. -/
theorem uniform_sector_form_transfer (H : ∀ n, E n →L[𝕜] E n) (γ : ℝ)
    (hsector : ∀ n (y : E n), γ * RCLike.re (inner (𝕜 := 𝕜) y (H n y)) ≤ ‖H n y‖ ^ 2)
    (x : ∀ n, E n) (hx : InGraphDomain H x) :
    γ * hamiltonianForm H x ≤ hamiltonianSquareForm H x := by
  have hq := sectorEnergy_summable H x hx
  have h := (hq.mul_left γ).tsum_le_tsum (fun n => hsector n (x n)) hx.2
  change (∑' n, γ * sectorEnergy H x n) ≤ hamiltonianSquareForm H x at h
  rw [hq.tsum_mul_left] at h
  exact h

/-- Positivity of sector blocks gives a positive form on the same graph
domain; the block positivity premise is explicit and not a new axiom. -/
theorem sectorwise_positive_form (H : ∀ n, E n →L[𝕜] E n)
    (hpos : ∀ n (y : E n), 0 ≤ RCLike.re (inner (𝕜 := 𝕜) y (H n y)))
    (x : ∀ n, E n) (hx : InGraphDomain H x) :
    0 ≤ hamiltonianForm H x := by
  exact (sectorEnergy_summable H x hx).hasSum.nonneg (fun n => hpos n (x n))

/-- Finite particle-support truncation of sector coordinates. -/
def truncate (K : ℕ) (x : ∀ n, E n) : ∀ n, E n :=
  fun n => if n < K then x n else 0

def OnFiniteParticleCore (x : ∀ n, E n) : Prop :=
  ∃ K, ∀ n, K ≤ n → x n = 0

theorem truncate_on_core (K : ℕ) (x : ∀ n, E n) : OnFiniteParticleCore (truncate K x) := by
  refine ⟨K, ?_⟩
  intro n hn
  simp [truncate, Nat.not_lt.mpr hn]

theorem finite_core_in_graphDomain (H : ∀ n, E n →L[𝕜] E n)
    (x : ∀ n, E n) (hx : OnFiniteParticleCore x) : InGraphDomain H x := by
  obtain ⟨K, hK⟩ := hx
  constructor
  · apply summable_of_ne_finset_zero (s := Finset.range K)
    intro n hn
    simp [hK n (Nat.le_of_not_gt (by simpa using hn))]
  · apply summable_of_ne_finset_zero (s := Finset.range K)
    intro n hn
    simp [hK n (Nat.le_of_not_gt (by simpa using hn))]

/-- Squared graph distance from x to its finite-support truncation. -/
def graphTruncationError (H : ∀ n, E n →L[𝕜] E n)
    (x : ∀ n, E n) (K : ℕ) : ℝ :=
  ∑' n, graphMass H (fun n => x n - truncate K x n) n

theorem graphTruncationError_eq_tail (H : ∀ n, E n →L[𝕜] E n)
    (x : ∀ n, E n) (hx : InGraphDomain H x) (K : ℕ) :
    graphTruncationError H x K = ∑' n, graphMass H x (n + K) := by
  have ht := graphMass_summable H (truncate K x)
    (finite_core_in_graphDomain H _ (truncate_on_core K x))
  have hdiff : (fun n => graphMass H (fun n => x n - truncate K x n) n) =
      (fun n => graphMass H x n - graphMass H (truncate K x) n) := by
    funext n
    by_cases hn : n < K <;> simp [graphMass, truncate, hn]
  rw [graphTruncationError, hdiff, (graphMass_summable H x hx).tsum_sub ht]
  have htSum : (∑' n, graphMass H (truncate K x) n) =
      ∑ n ∈ Finset.range K, graphMass H x n := by
    rw [tsum_eq_sum (s := Finset.range K)]
    · apply Finset.sum_congr rfl
      intro n hn
      simp [graphMass, truncate, Finset.mem_range.mp hn]
    · intro n hn
      simp [graphMass, truncate, Nat.not_lt.mpr
        (Nat.le_of_not_gt (by simpa using hn))]
  rw [htSum]
  have htail := (graphMass_summable H x hx).sum_add_tsum_nat_add K
  linarith

/-- Finite-particle truncations approximate every graph-domain vector in
squared graph distance, even when the block norms grow without bound.
This is the coordinate-level graph-core statement, not a self-adjointness proof. -/
theorem graphTruncationError_tendsto_zero (H : ∀ n, E n →L[𝕜] E n)
    (x : ∀ n, E n) (hx : InGraphDomain H x) :
    Tendsto (graphTruncationError H x) atTop (nhds 0) := by
  have hfun : graphTruncationError H x =
      (fun K => ∑' n, graphMass H x (n + K)) :=
    funext (graphTruncationError_eq_tail H x hx)
  rw [hfun]
  exact tendsto_sum_nat_add (graphMass H x)

end
end TorusLean.BosonBridge
