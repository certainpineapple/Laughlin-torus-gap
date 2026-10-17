import torus.shared.ThermalCoherentFockDirectSum
import FockFormDomain

/-! The algebraic finite-particle sum is a genuine graph core of the
self-adjoint Hilbert direct sum. The previously proved coordinate graph-domain
energy transfer is connected to the actual lp norm and inner product. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFockGraph
open TorusLean.Shared.ThermalCoherentFockDirectSum TorusLean.BosonBridge
open Filter
open scoped BigOperators Topology ENNReal
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℂ (E n)]

/-- The algebraic direct sum, inside the genuine Hilbert direct sum. -/
def finiteParticleCore : Submodule ℂ (lp E 2) where
  carrier := {x | OnFiniteParticleCore (fun n => x n)}
  zero_mem' := ⟨0,fun _ _ => rfl⟩
  add_mem' := by
    rintro x y ⟨K,hK⟩ ⟨L,hL⟩
    refine ⟨max K L,fun n hn => ?_⟩
    change x n+y n=0
    exact (congrArg₂ (fun a b : E n => a+b)
      (hK n (le_trans (le_max_left _ _) hn))
      (hL n (le_trans (le_max_right _ _) hn))).trans (add_zero 0)
  smul_mem' := by
    rintro c x ⟨K,hK⟩
    refine ⟨K,fun n hn => ?_⟩
    change c • x n=0
    exact (congrArg (fun a : E n => c • a) (hK n hn)).trans (smul_zero c)

/-- Canonical finite-particle truncation, as an actual Hilbert-sum vector. -/
def particleTruncate (K : ℕ) (x : lp E 2) : lp E 2 :=
  ∑ n ∈ Finset.range K, lp.single 2 n (x n)

theorem particleTruncate_apply (K : ℕ) (x : lp E 2) (n : ℕ) :
    particleTruncate K x n = if n<K then x n else 0 := by
  classical
  simp only [particleTruncate,lp.coeFn_sum,Finset.sum_apply,lp.coeFn_single,
    Finset.sum_pi_single,Finset.mem_range]

private theorem particleTruncate_mem_core (K : ℕ) (x : lp E 2) :
    particleTruncate K x ∈ finiteParticleCore :=
  ⟨K,fun n hn => (particleTruncate_apply K x n).trans (if_neg (Nat.not_lt.mpr hn))⟩

/-- This identifies the old coordinate graph condition with the actual domain. -/
theorem blockDomain_iff_coordinate_graph (H : ∀ n, E n →L[ℂ] E n) (x : lp E 2) :
    x ∈ blockDomain H ↔ InGraphDomain H (fun n => x n) := by
  have hx : InFockSpace (fun n => x n) := by
    simpa [InFockSpace] using (lp.memℓp x).summable (by norm_num : 0<(2:ℝ≥0∞).toReal)
  rw [mem_blockDomain_iff]
  exact (and_iff_right hx).symm

theorem finiteParticleCore_le_domain (H : ∀ n, E n →L[ℂ] E n) :
    finiteParticleCore ≤ (blockDirectSum H).domain := by
  intro x hx
  exact (blockDomain_iff_coordinate_graph H x).mpr
    (finite_core_in_graphDomain H (fun n => x n) hx)

private def truncateDomain (H : ∀ n, E n →L[ℂ] E n) (K : ℕ) (x : lp E 2) :
    (blockDirectSum H).domain :=
  ⟨particleTruncate K x,finiteParticleCore_le_domain H (particleTruncate_mem_core K x)⟩

private theorem block_truncate (H : ∀ n, E n →L[ℂ] E n)
    (K : ℕ) (x : (blockDirectSum H).domain) :
    blockDirectSum H (truncateDomain H K x.val) = particleTruncate K (blockDirectSum H x) := by
  apply lp.ext
  funext n
  change H n (particleTruncate K x.val n) = _
  rw [particleTruncate_apply,particleTruncate_apply,blockDirectSum_apply]
  split_ifs <;> simp only [map_zero]

private theorem particleTruncate_tendsto (x : lp E 2) :
    Tendsto (fun K => particleTruncate K x) atTop (𝓝 x) :=
  (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x).tendsto_sum_nat

/-- Both the physical vector and its operator output converge, not merely
coordinatewise convergence of finite-particle truncations. -/
theorem graph_truncation_tendsto (H : ∀ n, E n →L[ℂ] E n)
    (x : (blockDirectSum H).domain) :
    Tendsto (fun K => (particleTruncate K x.val,
      blockDirectSum H (truncateDomain H K x.val))) atTop
      (𝓝 (x.val,blockDirectSum H x)) := by
  simp only [block_truncate]
  exact (particleTruncate_tendsto x.val).prodMk_nhds
    (particleTruncate_tendsto (blockDirectSum H x))

variable [∀ n, CompleteSpace (E n)]

/-- The exact Mathlib HasCore statement for the algebraic finite-particle sum. -/
theorem blockDirectSum_has_finiteParticleCore (H : ∀ n, E n →L[ℂ] E n)
    (hH : ∀ n, IsSelfAdjoint (H n)) :
    (blockDirectSum H).HasCore finiteParticleCore := by
  refine ⟨finiteParticleCore_le_domain H,?_⟩
  have hclosed := blockDirectSum_isClosed H hH
  have hle : (blockDirectSum H).domRestrict finiteParticleCore ≤ blockDirectSum H :=
    LinearPMap.domRestrict_le
  have hclos := hclosed.isClosable.leIsClosable hle
  apply LinearPMap.eq_of_eq_graph
  rw [← hclos.graph_closure_eq_closure_graph]
  apply le_antisymm
  · exact Submodule.topologicalClosure_minimal _ (LinearPMap.le_graph_of_le hle) hclosed
  · intro z hz
    obtain ⟨x,rfl⟩ := (blockDirectSum H).mem_graph_iff'.mp hz
    refine mem_closure_of_tendsto (graph_truncation_tendsto H x) (Eventually.of_forall ?_)
    intro K
    apply ((blockDirectSum H).domRestrict finiteParticleCore).mem_graph_iff'.mpr
    refine ⟨⟨particleTruncate K x.val,particleTruncate_mem_core K x.val,
      (truncateDomain H K x.val).property⟩,?_⟩
    apply Prod.ext rfl
    exact LinearPMap.domRestrict_apply rfl

/-- The existing coordinate transfer now has the genuine operator's inner
product and norm on its precise domain. Its sector premise remains explicit
until the physical finite-sector gap is independently proved. -/
theorem directSum_uniform_form_transfer (H : ∀ n, E n →L[ℂ] E n) (γ : ℝ)
    (hsector : ∀ n (v : E n), γ*(inner ℂ v (H n v)).re ≤ ‖H n v‖^2)
    (x : (blockDirectSum H).domain) :
    γ*(inner ℂ x.val (blockDirectSum H x)).re ≤ ‖blockDirectSum H x‖^2 := by
  have hx := (blockDomain_iff_coordinate_graph H x.val).mp x.property
  have h := uniform_sector_form_transfer H γ hsector (fun n => x.val n) hx
  have hi : hamiltonianForm H (fun n => x.val n) =
      (inner ℂ x.val (blockDirectSum H x)).re := by
    exact (Complex.hasSum_re (lp.hasSum_inner x.val (blockDirectSum H x))).tsum_eq
  have hn : hamiltonianSquareForm H (fun n => x.val n) = ‖blockDirectSum H x‖^2 := by
    symm
    simpa [hamiltonianSquareForm,blockDirectSum_apply] using
      lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ℝ≥0∞).toReal) (blockDirectSum H x)
  rw [hi,hn] at h
  exact h

end TorusLean.Shared.ThermalCoherentFockGraph
