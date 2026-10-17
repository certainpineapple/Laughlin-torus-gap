import torus.shared.CellMeasure
import torus.shared.ContactDiagonal
import torus.shared.LLLThetaGauge
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The physical positive-charge LLL with its actual cell Hilbert structure

The carrier is the existing module of actual Gaussian-holomorphic magnetic
sections on the universal cover. The norm and inner product come from the
actual half-open-cell measure; finite dimension follows from the concrete
quadratic gauge injection into the independently classified theta space.
Neither a finite-coordinate model nor a dimension/continuity field is an
input. Only `finrank ≤ k*M` is asserted here.

Evaluation is the actual map `f ↦ f(R)`. Its continuity follows from the
derived finite dimension. Its operator norm is not yet identified with a
periodized reproducing kernel or with the paper's quantitative `k₂` bound.
-/

set_option autoImplicit false

noncomputable section

namespace TorusLean.Shared

open MeasureTheory
open scoped ComplexConjugate

/-- Physical LLL carrier, with positive charge required for its cell norm.
This definition wraps the actual raw section module, not a coordinate vector.
Using a separate definition keeps its physical cell norm on this carrier. -/
def LLL (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k] :=
  RawLLLModule G theta k

instance lllAddCommGroup (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k] :
    AddCommGroup (LLL G theta k) :=
  inferInstanceAs (AddCommGroup (RawLLLModule G theta k))

instance lllModule (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k] :
    Module ℂ (LLL G theta k) :=
  inferInstanceAs (Module ℂ (RawLLLModule G theta k))

/-- Forgetting the norm is the identity on actual functions and predicates. -/
def lllRawEquiv (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k] :
    LLL G theta k ≃ₗ[ℂ] RawLLLModule G theta k :=
  LinearEquiv.refl ℂ (RawLLLModule G theta k)

theorem lllRawEquiv_apply (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (f : LLL G theta k) : (lllRawEquiv G theta k f).val = f.val := rfl

/-- Positive-definite integral on the actual raw carrier. -/
@[instance_reducible]
def lllInnerCore (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k] :
    InnerProductSpace.Core ℂ (LLL G theta k) where
  inner f g := cellInner G k f.val g.val
  conj_inner_symm f g := cellInner_conj_symm G k g.val f.val
  re_inner_nonneg f := cellInner_self_re_nonneg G k f.val
  add_left f g h := by
    change cellInner G k (f.val + g.val) h.val =
      cellInner G k f.val h.val + cellInner G k g.val h.val
    exact cellInner_add_left G k f.val g.val h.val
      (rawLLL_continuous G theta k f) (rawLLL_continuous G theta k g)
      (rawLLL_continuous G theta k h)
  smul_left f g c := by
    change cellInner G k (c • f.val) g.val = conj c * cellInner G k f.val g.val
    exact cellInner_smul_left G k c f.val g.val
  definite f hf := by
    apply Subtype.ext
    exact (cellInner_self_eq_zero_iff G k (NeZero.pos k) f.val f.property.1).mp hf

private instance lllCoreInstance (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k] :
    InnerProductSpace.Core ℂ (LLL G theta k) := lllInnerCore G theta k

instance lllNormedAddCommGroup (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k] :
    NormedAddCommGroup (LLL G theta k) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (LLL G theta k) _ _ _
    (lllInnerCore G theta k)

instance lllInnerProductSpace (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k] :
    InnerProductSpace ℂ (LLL G theta k) :=
  InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℂ (LLL G theta k))

instance lllNormedSpace (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k] :
    NormedSpace ℂ (LLL G theta k) :=
  (lllInnerProductSpace G theta k).toNormedSpace

/-- The Hilbert inner product is definitionally the physical cell integral. -/
theorem lll_inner_eq_cellInner (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (f g : LLL G theta k) : inner ℂ f g = cellInner G k f.val g.val := rfl

theorem lll_norm_sq_eq_cellIntegral (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (f : LLL G theta k) :
    ‖f‖ ^ 2 = ∫ z, ‖f.val z‖ ^ 2 ∂cellMeasure G k := by
  have he : inner ℂ f f =
      ((∫ z, ‖f.val z‖ ^ 2 ∂cellMeasure G k : ℝ) : ℂ) :=
    (lll_inner_eq_cellInner G theta k f f).trans (cellInner_self G k f.val)
  have hn : ‖f‖ ^ 2 = (inner ℂ f f).re :=
    InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) f
  exact hn.trans ((congrArg Complex.re he).trans (Complex.ofReal_re _))

instance lllFiniteDimensional (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k] :
    FiniteDimensional ℂ (LLL G theta k) :=
  rawLLLSubmodule_finiteDimensional G theta k (NeZero.pos k)

/-- This is an upper bound, derived by injection. Equality is a separate theorem. -/
theorem lll_finrank_le (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k] :
    Module.finrank ℂ (LLL G theta k) ≤ k * G.M :=
  rawLLLSubmodule_finrank_le G theta k (NeZero.pos k)

/-- Completeness is derived from the physical norm and proved finite dimension. -/
instance lllCompleteSpace (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k] :
    CompleteSpace (LLL G theta k) :=
  FiniteDimensional.complete ℂ (LLL G theta k)

/-- Actual point evaluation, without a kernel or preferred twist as input. -/
def lllEvaluationLinearMap (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (R : ℂ) : LLL G theta k →ₗ[ℂ] ℂ where
  toFun f := f.val R
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Evaluation is bounded in the actual cell norm by derived finite dimension. -/
def lllEvaluation (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (R : ℂ) : LLL G theta k →L[ℂ] ℂ :=
  (lllEvaluationLinearMap G theta k R).toContinuousLinearMap

theorem lllEvaluation_apply (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (R : ℂ) (f : LLL G theta k) : lllEvaluation G theta k R f = f.val R := rfl

/-- A real evaluation bound with the actual operator norm. The geometric
identification/quantitative estimate of this norm is still pending. -/
theorem lllEvaluation_bound (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (R : ℂ) (f : LLL G theta k) :
    ‖f.val R‖ ≤ ‖lllEvaluation G theta k R‖ * ‖f‖ :=
  (lllEvaluation G theta k R).le_opNorm f

#print axioms lllRawEquiv_apply
#print axioms lllInnerCore
#print axioms lllNormedAddCommGroup
#print axioms lllNormedSpace
#print axioms lllInnerProductSpace
#print axioms lll_inner_eq_cellInner
#print axioms lll_norm_sq_eq_cellIntegral
#print axioms lllFiniteDimensional
#print axioms lll_finrank_le
#print axioms lllCompleteSpace
#print axioms lllEvaluation
#print axioms lllEvaluation_apply
#print axioms lllEvaluation_bound

end TorusLean.Shared
