import torus.shared.RelativeJetMapFamily
import torus.shared.RelativeJetGramSeries

/-!
Finite Hilbert-sum bookkeeping for the actual jets. The `_of_entries`
statements below are explicitly conditional composition lemmas: they are
NOT an independent identification of the true Gram with its lattice sum.
That identity must be proved separately before their frame bound is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.RelativeJetMap
open TorusLean.Shared.RelativeJetGramSeries TorusLean.Shared.BosonSystole20Scalar
open TorusLean.Fermion.LatticePacking
open scoped TensorProduct ComplexConjugate BigOperators

/-- Consecutive finite relative degrees, each retaining the full charge4
COM space. The norm is the actual Hilbert sum, not the Pi sup norm. -/
abbrev RelativeCOMTruncation (G : Geometry) (theta : Twist) (D : ℕ) :=
  PiLp 2 (fun _ : Fin (D+1) => LLL G theta 4)

def relativeJetTruncation (G : Geometry) (theta : Twist) (D : ℕ) :
    (LLL G theta 2 ⊗[ℂ] LLL G theta 2) →L[ℂ] RelativeCOMTruncation G theta D :=
  (PiLp.continuousLinearEquiv 2 ℂ _).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun d : Fin (D+1) => relativeJet G theta 2 2 d.val))

@[simp] theorem relativeJetTruncation_apply (G : Geometry) (theta : Twist) (D : ℕ)
    (ψ : LLL G theta 2 ⊗[ℂ] LLL G theta 2) (d : Fin (D+1)) :
    relativeJetTruncation G theta D ψ d = relativeJet G theta 2 2 d.val ψ := rfl

/-- Exact original cell-integral energy of the consecutive-degree family. -/
theorem relativeJetTruncation_norm_sq (G : Geometry) (theta : Twist) (D : ℕ)
    (ψ : LLL G theta 2 ⊗[ℂ] LLL G theta 2) :
    ‖relativeJetTruncation G theta D ψ‖^2 =
      ∑ d : Fin (D+1), ∫ C, ‖TorusLean.Geometry.localNormalJet 2 2 d.val
        (rawPairFunction G theta 2 2 ψ) C‖^2 ∂cellMeasure G 4 := by
  rw [PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_congr rfl
  intro d _
  exact relativeJet_cell_norm_sq G theta 2 2 d.val ψ

/-- Actual finite-sum adjoint, before any Gram formula or estimate. -/
theorem relativeJetTruncation_adjoint (G : Geometry) (theta : Twist) (D : ℕ)
    (f : RelativeCOMTruncation G theta D) :
    (relativeJetTruncation G theta D).adjoint f =
      ∑ m : Fin (D+1), (relativeJet G theta 2 2 m.val).adjoint (f m) := by
  apply ext_inner_right ℂ
  intro ψ
  rw [ContinuousLinearMap.adjoint_inner_left, sum_inner, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro m _
  exact (ContinuousLinearMap.adjoint_inner_left (relativeJet G theta 2 2 m.val) ψ (f m)).symm

/-- Coordinate matrix of the genuine full-COM JJ†. -/
theorem relativeJetTruncation_gram_coordinate (G : Geometry) (theta : Twist) (D : ℕ)
    (f : RelativeCOMTruncation G theta D) (j : Fin (D+1)) :
    relativeJetTruncation G theta D ((relativeJetTruncation G theta D).adjoint f) j =
      ∑ m : Fin (D+1), relativeJet G theta 2 2 j.val
        ((relativeJet G theta 2 2 m.val).adjoint (f m)) := by
  rw [relativeJetTruncation_apply, relativeJetTruncation_adjoint, map_sum]

/-- Finite matrix inner-product expansion without a lattice identity. -/
theorem relativeJetTruncation_gram_inner (G : Geometry) (theta : Twist) (D : ℕ)
    (f : RelativeCOMTruncation G theta D) :
    inner ℂ f (relativeJetTruncation G theta D ((relativeJetTruncation G theta D).adjoint f)) =
      ∑ j : Fin (D+1), ∑ m : Fin (D+1), inner ℂ (f j)
        (relativeJet G theta 2 2 j.val ((relativeJet G theta 2 2 m.val).adjoint (f m))) := by
  rw [PiLp.inner_apply]
  simp_rw [relativeJetTruncation_gram_coordinate, inner_sum]

/-- Conditional bookkeeping only: the separately proved lattice entry
identity is supplied explicitly and used once to identify the true Gram. -/
theorem relativeJetTruncation_gram_error_of_entries (G : Geometry) (theta : Twist)
    (D : ℕ) (hD : D ≤ 16) (hL : 20 ≤ systole G)
    (hentries : ∀ j m : Fin (D+1),
      (relativeJet G theta 2 2 j.val).comp (relativeJet G theta 2 2 m.val).adjoint =
        relativeGramEntry G theta j.val m.val)
    (f : RelativeCOMTruncation G theta D) :
    |‖(relativeJetTruncation G theta D).adjoint f‖^2 - ‖f‖^2| ≤ allowance * ‖f‖^2 := by
  classical
  have hentry (j m : Fin (D+1)) :
      relativeJet G theta 2 2 j.val ((relativeJet G theta 2 2 m.val).adjoint (f m)) =
        relativeGramEntry G theta j.val m.val (f m) :=
    congrArg (fun A : LLL G theta 4 →L[ℂ] LLL G theta 4 => A (f m)) (hentries j m)
  have hid : (∑ j : Fin (D+1), ∑ m : Fin (D+1), inner ℂ (f j)
      ((if j = m then ContinuousLinearMap.id ℂ (LLL G theta 4) else 0) (f m))) =
        inner ℂ f f := by
    simp only [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro j _
    have hi (m : Fin (D+1)) : inner ℂ (f j)
        ((if j = m then ContinuousLinearMap.id ℂ (LLL G theta 4) else 0) (f m)) =
          if j = m then inner ℂ (f j) (f j) else 0 := by
      split_ifs with h
      · subst m; rfl
      · simp
    simp_rw [hi]
    simp
  have heq : (∑ j : Fin (D+1), ∑ m : Fin (D+1), inner ℂ (f j)
      ((relativeGramEntry G theta j m -
        (if j = m then ContinuousLinearMap.id ℂ (LLL G theta 4) else 0)) (f m))) =
        inner ℂ ((relativeJetTruncation G theta D).adjoint f)
          ((relativeJetTruncation G theta D).adjoint f) - inner ℂ f f := by
    simp only [ContinuousLinearMap.sub_apply, inner_sub_right, Finset.sum_sub_distrib]
    rw [hid, ContinuousLinearMap.adjoint_inner_left]
    rw [relativeJetTruncation_gram_inner]
    simp_rw [hentry]
  have h := relativeGramEntry_common_allowance G theta D hD hL (fun j => f j)
  rw [heq, ← PiLp.norm_sq_eq_of_L2] at h
  have hre := (Complex.abs_re_le_norm
    (inner ℂ ((relativeJetTruncation G theta D).adjoint f)
      ((relativeJetTruncation G theta D).adjoint f) - inner ℂ f f)).trans h
  have hn₁ : ‖(relativeJetTruncation G theta D).adjoint f‖^2 =
      (inner ℂ ((relativeJetTruncation G theta D).adjoint f)
        ((relativeJetTruncation G theta D).adjoint f)).re :=
    InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _
  have hn₂ : ‖f‖^2 = (inner ℂ f f).re := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _
  rw [Complex.sub_re, ← hn₁, ← hn₂] at hre
  exact hre

/-- The conditional error budget gives the actual J† energy upper bound. -/
theorem relativeJetTruncation_adjoint_bound_of_entries (G : Geometry) (theta : Twist)
    (D : ℕ) (hD : D ≤ 16) (hL : 20 ≤ systole G)
    (hentries : ∀ j m : Fin (D+1),
      (relativeJet G theta 2 2 j.val).comp (relativeJet G theta 2 2 m.val).adjoint =
        relativeGramEntry G theta j.val m.val)
    (f : RelativeCOMTruncation G theta D) :
    ‖(relativeJetTruncation G theta D).adjoint f‖^2 ≤ (1+allowance) * ‖f‖^2 := by
  have h := (abs_le.mp (relativeJetTruncation_gram_error_of_entries G theta D hD hL hentries f)).2
  nlinarith

/-- Adjoint isometry transfers the conditional full-output bound back to
actual input tensors, with no extra number-of-COM-modes factor. -/
theorem relativeJetTruncation_opNorm_of_entries (G : Geometry) (theta : Twist)
    (D : ℕ) (hD : D ≤ 16) (hL : 20 ≤ systole G)
    (hentries : ∀ j m : Fin (D+1),
      (relativeJet G theta 2 2 j.val).comp (relativeJet G theta 2 2 m.val).adjoint =
        relativeGramEntry G theta j.val m.val) :
    ‖relativeJetTruncation G theta D‖ ≤ Real.sqrt (1+allowance) := by
  have hB : 0 ≤ 1+allowance := by unfold allowance; norm_num
  have h := ContinuousLinearMap.opNorm_le_bound (relativeJetTruncation G theta D).adjoint
    (Real.sqrt_nonneg (1+allowance)) (fun f => ?_)
  · simpa using h
  · apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hB]
    exact relativeJetTruncation_adjoint_bound_of_entries G theta D hD hL hentries f

/-- Conditional input-frame energy statement on the actual full tensor. -/
theorem relativeJetTruncation_energy_of_entries (G : Geometry) (theta : Twist)
    (D : ℕ) (hD : D ≤ 16) (hL : 20 ≤ systole G)
    (hentries : ∀ j m : Fin (D+1),
      (relativeJet G theta 2 2 j.val).comp (relativeJet G theta 2 2 m.val).adjoint =
        relativeGramEntry G theta j.val m.val)
    (ψ : LLL G theta 2 ⊗[ℂ] LLL G theta 2) :
    ‖relativeJetTruncation G theta D ψ‖^2 ≤ (1+allowance) * ‖ψ‖^2 := by
  have h := ((relativeJetTruncation G theta D).le_opNorm ψ).trans
    (mul_le_mul_of_nonneg_right
      (relativeJetTruncation_opNorm_of_entries G theta D hD hL hentries) (norm_nonneg _))
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr h
  rw [mul_pow, Real.sq_sqrt (by unfold allowance; norm_num : 0 ≤ 1+allowance)] at hs
  exact hs

/-- Conditional J†J quadratic form bound in the original tensor norm. -/
theorem relativeJetTruncation_input_form_of_entries (G : Geometry) (theta : Twist)
    (D : ℕ) (hD : D ≤ 16) (hL : 20 ≤ systole G)
    (hentries : ∀ j m : Fin (D+1),
      (relativeJet G theta 2 2 j.val).comp (relativeJet G theta 2 2 m.val).adjoint =
        relativeGramEntry G theta j.val m.val)
    (ψ : LLL G theta 2 ⊗[ℂ] LLL G theta 2) :
    (inner ℂ ψ ((relativeJetTruncation G theta D).adjoint
      (relativeJetTruncation G theta D ψ))).re ≤ (1+allowance) * ‖ψ‖^2 := by
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hn : ‖relativeJetTruncation G theta D ψ‖^2 =
      (inner ℂ (relativeJetTruncation G theta D ψ) (relativeJetTruncation G theta D ψ)).re :=
    InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _
  rw [← hn]
  exact relativeJetTruncation_energy_of_entries G theta D hD hL hentries ψ

end TorusLean.Shared.RelativeJetMap
