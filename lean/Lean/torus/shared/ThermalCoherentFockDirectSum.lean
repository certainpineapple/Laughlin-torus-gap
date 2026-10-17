import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! A genuine densely defined self-adjoint Hilbert direct sum. The blocks
may have unbounded norms as the particle index grows. Its domain is exactly
square-summability of the actual block outputs. No spectral-gap estimate is
assumed or concluded in this generic operator construction. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFockDirectSum
open scoped BigOperators Topology ENNReal
open Filter
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℂ (E n)]

/-- Actual graph-domain submodule inside the already completed Hilbert sum. -/
def blockDomain (H : ∀ n, E n →L[ℂ] E n) : Submodule ℂ (lp E 2) where
  carrier := {x | Memℓp (fun n => H n (x n)) 2}
  zero_mem' := by
    change Memℓp (fun n => H n 0) 2
    rw [show (fun n => H n 0) = (0 : ∀ n, E n) by
      funext n; exact map_zero (H n)]
    exact zero_memℓp
  add_mem' := by
    intro x y hx hy
    change Memℓp (fun n => H n (x n+y n)) 2
    rw [show (fun n => H n (x n+y n)) =
        (fun n => H n (x n)) + (fun n => H n (y n)) by
      funext n; exact map_add (H n) _ _]
    exact hx.add hy
  smul_mem' := by
    intro c x hx
    change Memℓp (fun n => H n (c • x n)) 2
    rw [show (fun n => H n (c • x n)) = c • (fun n => H n (x n)) by
      funext n; exact map_smul (H n) c _]
    exact hx.const_smul c

/-- No totalized unbounded action: the input explicitly belongs to blockDomain. -/
def blockDirectSum (H : ∀ n, E n →L[ℂ] E n) : lp E 2 →ₗ.[ℂ] lp E 2 where
  domain := blockDomain H
  toFun :=
    { toFun := fun x => ⟨fun n => H n (x.val n),x.property⟩
      map_add' := fun x y => by apply lp.ext; funext n; exact map_add (H n) _ _
      map_smul' := fun c x => by apply lp.ext; funext n; exact map_smul (H n) c _ }

theorem blockDirectSum_apply (H : ∀ n, E n →L[ℂ] E n)
    (x : (blockDirectSum H).domain) (n : ℕ) :
    blockDirectSum H x n = H n (x.val n) := rfl

/-- In particular the domain is D(H), not the stronger D(H squared). -/
theorem mem_blockDomain_iff (H : ∀ n, E n →L[ℂ] E n) (x : lp E 2) :
    x ∈ blockDomain H ↔ Summable (fun n => ‖H n (x n)‖^2) := by
  change Memℓp _ 2 ↔ _
  simpa using (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num) :
    Memℓp (fun n => H n (x n)) 2 ↔ _)

private theorem block_single_coordinates (H : ∀ n, E n →L[ℂ] E n)
    (n : ℕ) (v : E n) :
    (fun m => H m (lp.single 2 n v m)) = lp.single 2 n (H n v) := by
  funext m
  by_cases hm : m=n
  · subst m; simp only [lp.single_apply_self]
  · simp only [lp.single_apply_ne 2 n v hm,
      lp.single_apply_ne 2 n (H n v) hm,map_zero]

theorem single_mem_blockDomain (H : ∀ n, E n →L[ℂ] E n) (n : ℕ) (v : E n) :
    lp.single 2 n v ∈ blockDomain H := by
  change Memℓp _ 2
  rw [block_single_coordinates]
  exact lp.memℓp _

private theorem blockDirectSum_single (H : ∀ n, E n →L[ℂ] E n)
    (n : ℕ) (v : E n) :
    blockDirectSum H ⟨lp.single 2 n v,single_mem_blockDomain H n v⟩ =
      lp.single 2 n (H n v) := by
  apply lp.ext
  exact block_single_coordinates H n v

/-- Finite particle-support vectors already make the actual operator domain dense. -/
theorem blockDirectSum_dense_domain (H : ∀ n, E n →L[ℂ] E n) :
    Dense ((blockDirectSum H).domain : Set (lp E 2)) := by
  intro x
  refine mem_closure_of_tendsto (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) x)
    (Eventually.of_forall ?_)
  intro s
  exact (blockDomain H).sum_mem fun n _ => single_mem_blockDomain H n (x n)

variable [∀ n, CompleteSpace (E n)]

/-- The equality of inner products follows from actual summable Hilbert pairings. -/
theorem blockDirectSum_formalAdjoint (H : ∀ n, E n →L[ℂ] E n)
    (hH : ∀ n, IsSelfAdjoint (H n)) :
    (blockDirectSum H).IsFormalAdjoint (blockDirectSum H) := by
  intro x y
  simp only [lp.inner_eq_tsum,blockDirectSum_apply]
  apply tsum_congr
  intro n
  exact (hH n).isSymmetric (x.val n) (y.val n)

private theorem adjoint_coordinate (H : ∀ n, E n →L[ℂ] E n)
    (hH : ∀ n, IsSelfAdjoint (H n))
    (y : (blockDirectSum H).adjoint.domain) (n : ℕ) :
    (blockDirectSum H).adjoint y n = H n (y.val n) := by
  apply ext_inner_right ℂ
  intro v
  have h := LinearPMap.adjoint_isFormalAdjoint (blockDirectSum_dense_domain H) y
    ⟨lp.single 2 n v,single_mem_blockDomain H n v⟩
  rw [blockDirectSum_single,lp.inner_single_right,lp.inner_single_right] at h
  exact h.trans ((hH n).isSymmetric (y.val n) v).symm

/-- Genuine self-adjointness, with equality of adjoint domains proved using
single-sector tests. No uniform bound on the block operator norms is needed. -/
theorem blockDirectSum_selfAdjoint (H : ∀ n, E n →L[ℂ] E n)
    (hH : ∀ n, IsSelfAdjoint (H n)) : IsSelfAdjoint (blockDirectSum H) := by
  apply LinearPMap.isSelfAdjoint_def.mpr
  apply le_antisymm
  · refine ⟨?_,?_⟩
    · intro y hy
      change Memℓp (fun n => H n (y n)) 2
      have he : (fun n => H n (y n)) = (blockDirectSum H).adjoint ⟨y,hy⟩ :=
        funext fun n => (adjoint_coordinate H hH ⟨y,hy⟩ n).symm
      rw [he]
      exact lp.memℓp _
    · intro x y hxy
      apply lp.ext
      funext n
      rw [adjoint_coordinate H hH,blockDirectSum_apply]
      exact congrArg (fun u : lp E 2 => H n (u n)) hxy
  · exact (blockDirectSum_formalAdjoint H hH).le_adjoint (blockDirectSum_dense_domain H)

/-- Closedness is now a conclusion of actual self-adjointness. -/
theorem blockDirectSum_isClosed (H : ∀ n, E n →L[ℂ] E n)
    (hH : ∀ n, IsSelfAdjoint (H n)) : (blockDirectSum H).IsClosed :=
  (blockDirectSum_selfAdjoint H hH).isClosed

end TorusLean.Shared.ThermalCoherentFockDirectSum
