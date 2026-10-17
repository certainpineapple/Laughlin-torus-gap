import torus.shared.RelativeJetGramKernelSum
import torus.shared.RelativeJetMapFamilyBudget
import torus.shared.PlaneJetFiniteGram

/-!
Every fixed finite relative-jet family is asymptotically a full-COM frame.
The physical input is the complete charge-two tensor product, and every
output coordinate is the complete charge-four LLL. The sole finite-size
factor below is the number of retained relative degrees; there is no COM
dimension factor. These theorems do not identify any CAR contraction row.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.RelativeJetFrameAsymptotic
open TorusLean.Shared.RelativeJetMap TorusLean.Shared.RelativeJetGramKernelSum
open TorusLean.Shared.RelativeJetGramSeries TorusLean.Shared.PlaneJetMixedBounds
open TorusLean.Shared.PlaneJetFiniteGram TorusLean.Fermion.LatticePacking
open Filter Topology
open scoped TensorProduct BigOperators

/-- Arbitrary fixed-order operator entry estimate on the whole COM space. -/
theorem relativeGramEntry_error_le (G : Geometry) (theta : Twist)
    (j m : ℕ) (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G) :
    ‖relativeGramEntry G theta j m -
      (if j = m then ContinuousLinearMap.id ℂ (LLL G theta 4) else 0)‖ ≤
      mixedCoefficientEnvelope j m * gaussianConstant * Real.exp (-L^2 / 8) := by
  classical
  have hG := hL1.trans hL
  have hL0 : 0 ≤ L := le_trans zero_le_one hL1
  have hs := hasSum_ite_sub_hasSum (relativeImageOperator_summable G theta j m hG).hasSum
    (0 : ℤ × ℤ)
  rw [relativeImageOperator_zero] at hs
  have hb : ∀ p : ℤ × ℤ,
      ‖if p = 0 then (0 : LLL G theta 4 →L[ℂ] LLL G theta 4)
        else relativeImageOperator G theta j m p‖ ≤
      mixedCoefficientEnvelope j m * gaussianTail G 0 L p := by
    intro p
    by_cases hp : p = 0
    · simp only [hp, ite_true, norm_zero]
      apply mul_nonneg (mixedCoefficientEnvelope_nonneg j m)
      unfold gaussianTail
      split_ifs <;> positivity
    · have hl := (systole_ge_iff G L).mp hL p hp
      simp only [hp, ite_false, gaussianTail, sub_zero, ite_eq_left hl]
      exact (relativeImageOperator_norm_le G theta j m p).trans
        (mixedCoefficient_norm_le j m (period G p))
  have hn := hs.norm_le_of_bounded
    ((gaussianTail_summable G hG 0 L hL0).hasSum.mul_left (mixedCoefficientEnvelope j m)) hb
  have h := hn.trans (mul_le_mul_of_nonneg_left (gaussianTail_bound G hG 0 L hL0)
    (mixedCoefficientEnvelope_nonneg j m))
  simpa only [relativeGramEntry, mul_assoc, mul_comm gaussianConstant] using h

/-- A uniform entry budget for every finite degree, with no upper restriction on D. -/
theorem relativeGramEntry_finite_error_le (G : Geometry) (theta : Twist)
    (D : ℕ) (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G)
    (j m : Fin (D+1)) :
    ‖relativeGramEntry G theta j m -
      (if j = m then ContinuousLinearMap.id ℂ (LLL G theta 4) else 0)‖ ≤
      finiteGramError D L := by
  have h := relativeGramEntry_error_le G theta j m L hL1 hL
  have h' : ‖relativeGramEntry G theta j m -
      (if j = m then ContinuousLinearMap.id ℂ (LLL G theta 4) else 0)‖ ≤
      mixedCoefficientEnvelope j m * gaussianConstant * Real.exp (-L^2/8) := by
    simpa only [Fin.val_inj] using h
  exact h'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mixedCoefficientEnvelope_le_finite D j m)
      gaussianConstant_nonneg) (Real.exp_nonneg _))

/-- Explicit full-family budget C_D exp(-L²/8), where C_D is finite and
independent of geometry, twist, and COM dimension. -/
def relativeFrameError (D : ℕ) (L : ℝ) : ℝ :=
  finiteGramError D L * (D+1 : ℕ)

theorem relativeFrameError_nonneg (D : ℕ) (L : ℝ) : 0 ≤ relativeFrameError D L :=
  mul_nonneg (finiteGramError_nonneg D L) (Nat.cast_nonneg _)

theorem relativeFrameError_eq (D : ℕ) (L : ℝ) :
    relativeFrameError D L =
      (finiteGramConstant D * gaussianConstant * (D+1 : ℕ)) * Real.exp (-L^2/8) := by
  unfold relativeFrameError finiteGramError
  ring

theorem relativeGramEntry_quadratic_le (G : Geometry) (theta : Twist)
    (D : ℕ) (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G)
    (f : Fin (D+1) → LLL G theta 4) :
    ‖∑ j : Fin (D+1), ∑ m : Fin (D+1), inner ℂ (f j)
      ((relativeGramEntry G theta j m -
        (if j = m then ContinuousLinearMap.id ℂ (LLL G theta 4) else 0)) (f m))‖ ≤
      relativeFrameError D L * ∑ j, ‖f j‖^2 := by
  classical
  simpa only [Fintype.card_fin, relativeFrameError] using
    operator_matrix_quadratic_bound
      (fun j m : Fin (D+1) => relativeGramEntry G theta j m -
        (if j = m then ContinuousLinearMap.id ℂ (LLL G theta 4) else 0)) f
      (finiteGramError D L) (finiteGramError_nonneg D L)
      (relativeGramEntry_finite_error_le G theta D L hL1 hL)

/-- The true JJ† quadratic error, using the proved physical entry identity. -/
theorem relativeJetTruncation_gram_error (G : Geometry) (theta : Twist)
    (D : ℕ) (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G)
    (f : RelativeCOMTruncation G theta D) :
    |‖(relativeJetTruncation G theta D).adjoint f‖^2 - ‖f‖^2| ≤
      relativeFrameError D L * ‖f‖^2 := by
  classical
  have hentry (j m : Fin (D+1)) :
      relativeJet G theta 2 2 j.val ((relativeJet G theta 2 2 m.val).adjoint (f m)) =
        relativeGramEntry G theta j.val m.val (f m) :=
    congrArg (fun A : LLL G theta 4 →L[ℂ] LLL G theta 4 => A (f m)) (relativeJet_comp_adjoint_eq_entry G theta j m (hL1.trans hL))
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
  have h := relativeGramEntry_quadratic_le G theta D L hL1 hL (fun j => f j)
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

/-- Two-sided almost-isometry of the actual synthesis map J†. -/
theorem relativeJetTruncation_two_sided (G : Geometry) (theta : Twist)
    (D : ℕ) (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G)
    (f : RelativeCOMTruncation G theta D) :
    (1-relativeFrameError D L) * ‖f‖^2 ≤
        ‖(relativeJetTruncation G theta D).adjoint f‖^2 ∧
    ‖(relativeJetTruncation G theta D).adjoint f‖^2 ≤
        (1+relativeFrameError D L) * ‖f‖^2 := by
  have h := abs_le.mp (relativeJetTruncation_gram_error G theta D L hL1 hL f)
  constructor <;> nlinarith [h.1, h.2]

/-- Actual input operator norm, with no COM mode-count loss. -/
theorem relativeJetTruncation_opNorm (G : Geometry) (theta : Twist)
    (D : ℕ) (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G) :
    ‖relativeJetTruncation G theta D‖ ≤ Real.sqrt (1+relativeFrameError D L) := by
  have hB : 0 ≤ 1+relativeFrameError D L := by linarith [relativeFrameError_nonneg D L]
  have h := ContinuousLinearMap.opNorm_le_bound (relativeJetTruncation G theta D).adjoint
    (Real.sqrt_nonneg (1+relativeFrameError D L)) (fun f => ?_)
  · simpa using h
  · apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
    rw [mul_pow, Real.sq_sqrt hB]
    exact (relativeJetTruncation_two_sided G theta D L hL1 hL f).2

/-- Fixed-degree frame inequality on the complete physical input tensor. -/
theorem relativeJetTruncation_energy (G : Geometry) (theta : Twist)
    (D : ℕ) (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G)
    (ψ : LLL G theta 2 ⊗[ℂ] LLL G theta 2) :
    ‖relativeJetTruncation G theta D ψ‖^2 ≤ (1+relativeFrameError D L) * ‖ψ‖^2 := by
  have h := ((relativeJetTruncation G theta D).le_opNorm ψ).trans
    (mul_le_mul_of_nonneg_right
      (relativeJetTruncation_opNorm G theta D L hL1 hL) (norm_nonneg _))
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr h
  rw [mul_pow, Real.sq_sqrt (by linarith [relativeFrameError_nonneg D L] :
    0 ≤ 1+relativeFrameError D L)] at hs
  exact hs

/-- The same bound in the original charge-four cell integrals. -/
theorem relativeJetTruncation_cell_energy (G : Geometry) (theta : Twist)
    (D : ℕ) (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G)
    (ψ : LLL G theta 2 ⊗[ℂ] LLL G theta 2) :
    (∑ d : Fin (D+1), ∫ C, ‖TorusLean.Geometry.localNormalJet 2 2 d.val
      (rawPairFunction G theta 2 2 ψ) C‖^2 ∂cellMeasure G 4) ≤
      (1+relativeFrameError D L) * ‖ψ‖^2 := by
  rw [← relativeJetTruncation_norm_sq]
  exact relativeJetTruncation_energy G theta D L hL1 hL ψ

theorem relativeFrameError_tendsto (D : ℕ) :
    Tendsto (relativeFrameError D) atTop (𝓝 0) := finiteGramOperatorError_tendsto D

/-- Uniformity includes arbitrary varying geometries and twists: only the
actual systole must tend to infinity. -/
theorem relativeFrameError_systole_tendsto {ι : Type*} {l : Filter ι}
    (G : ι → Geometry) (D : ℕ) (hG : Tendsto (fun a => systole (G a)) l atTop) :
    Tendsto (fun a => relativeFrameError D (systole (G a))) l (𝓝 0) :=
  (relativeFrameError_tendsto D).comp hG

/-- Every prescribed positive tolerance has one geometry-independent threshold. -/
theorem relativeFrameError_exists_threshold (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ x : ℝ, L ≤ x → relativeFrameError D x ≤ ε := by
  have h := (relativeFrameError_tendsto D).eventually (gt_mem_nhds hε)
  obtain ⟨L, hL⟩ := eventually_atTop.mp h
  refine ⟨max 1 L, le_max_left _ _, fun x hx => ?_⟩
  exact (hL x ((le_max_right _ _).trans hx)).le

/-- Unconditional asymptotic frame theorem at any fixed finite degree. -/
theorem relativeJetTruncation_exists_threshold (D : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (G : Geometry) (theta : Twist), L ≤ systole G →
      (∀ f : RelativeCOMTruncation G theta D,
        |‖(relativeJetTruncation G theta D).adjoint f‖^2 - ‖f‖^2| ≤ ε * ‖f‖^2) ∧
      (∀ ψ : LLL G theta 2 ⊗[ℂ] LLL G theta 2,
        ‖relativeJetTruncation G theta D ψ‖^2 ≤ (1+ε) * ‖ψ‖^2) := by
  obtain ⟨L, hL1, hL⟩ := relativeFrameError_exists_threshold D ε hε
  refine ⟨L, hL1, fun G theta hG => ?_⟩
  have hE := hL (systole G) hG
  constructor
  · intro f
    exact (relativeJetTruncation_gram_error G theta D (systole G)
      (hL1.trans hG) le_rfl f).trans (mul_le_mul_of_nonneg_right hE (sq_nonneg _))
  · intro ψ
    exact (relativeJetTruncation_energy G theta D (systole G)
      (hL1.trans hG) le_rfl ψ).trans
      (mul_le_mul_of_nonneg_right (by linarith : 1 + relativeFrameError D (systole G) ≤ 1 + ε) (sq_nonneg _))

/-- The fermionic downstream finite relative-degree requirement is D=22.
No claim about the original CAR C_(d+1) row is included in this theorem. -/
theorem relativeJetTruncation_degree22_exists_threshold (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (G : Geometry) (theta : Twist), L ≤ systole G →
      (∀ f : RelativeCOMTruncation G theta 22,
        |‖(relativeJetTruncation G theta 22).adjoint f‖^2 - ‖f‖^2| ≤ ε * ‖f‖^2) ∧
      (∀ ψ : LLL G theta 2 ⊗[ℂ] LLL G theta 2,
        ‖relativeJetTruncation G theta 22 ψ‖^2 ≤ (1+ε) * ‖ψ‖^2) :=
  relativeJetTruncation_exists_threshold 22 ε hε

#print axioms relativeGramEntry_error_le
#print axioms relativeJetTruncation_gram_error
#print axioms relativeJetTruncation_opNorm
#print axioms relativeJetTruncation_cell_energy
#print axioms relativeFrameError_tendsto
#print axioms relativeJetTruncation_degree22_exists_threshold

/-- A finite matrix of bounded operators acts on the true Hilbert sum.
Its norm loses only the finite matrix size, not the dimension of E. -/
theorem operator_matrix_opNorm_le {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : PiLp 2 (fun _ : ι => E) →L[ℂ] PiLp 2 (fun _ : ι => E))
    (A : ι → ι → E →L[ℂ] E) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ j m, ‖A j m‖ ≤ C)
    (hT : ∀ (f : PiLp 2 (fun _ : ι => E)) j, T f j = ∑ m, A j m (f m)) :
    ‖T‖ ≤ C * (Fintype.card ι : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound T
    (mul_nonneg hC (Nat.cast_nonneg _))
  intro f
  have hb (j : ι) : ‖T f j‖ ≤ C * ∑ m, ‖f m‖ := by
    rw [hT]
    calc
      _ ≤ ∑ m, ‖A j m (f m)‖ := norm_sum_le _ _
      _ ≤ ∑ m, C * ‖f m‖ := Finset.sum_le_sum fun m _ =>
        ((A j m).le_opNorm (f m)).trans
          (mul_le_mul_of_nonneg_right (hA j m) (norm_nonneg _))
      _ = _ := by rw [Finset.mul_sum]
  have hs : (∑ m, ‖f m‖)^2 ≤ (Fintype.card ι : ℝ) * ∑ m, ‖f m‖^2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : ι => (1 : ℝ)) (fun m => ‖f m‖)
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (mul_nonneg hC (Nat.cast_nonneg _)) (norm_nonneg _))).mp
  rw [mul_pow]
  calc
    ‖T f‖^2 = ∑ j, ‖T f j‖^2 := PiLp.norm_sq_eq_of_L2 _ _
    _ ≤ ∑ _j : ι, (C * ∑ m, ‖f m‖)^2 := by
      apply Finset.sum_le_sum
      intro j _
      exact (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg hC (Finset.sum_nonneg fun _ _ => norm_nonneg _))).mpr (hb j)
    _ = (Fintype.card ι : ℝ) * C^2 * (∑ m, ‖f m‖)^2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_pow]
      ring
    _ ≤ (Fintype.card ι : ℝ) * C^2 *
        ((Fintype.card ι : ℝ) * ∑ m, ‖f m‖^2) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
    _ = (C * (Fintype.card ι : ℝ))^2 * ‖f‖^2 := by
      rw [PiLp.norm_sq_eq_of_L2]
      ring

/-- The actual complete-output Gram error operator. -/
def relativeJetGramErrorOperator (G : Geometry) (theta : Twist) (D : ℕ) :
    RelativeCOMTruncation G theta D →L[ℂ] RelativeCOMTruncation G theta D :=
  (relativeJetTruncation G theta D).comp (relativeJetTruncation G theta D).adjoint -
    ContinuousLinearMap.id ℂ (RelativeCOMTruncation G theta D)

theorem relativeJetGramErrorOperator_coordinate (G : Geometry) (theta : Twist)
    (D : ℕ) (hG : 1 ≤ systole G) (f : RelativeCOMTruncation G theta D)
    (j : Fin (D+1)) :
    relativeJetGramErrorOperator G theta D f j =
      ∑ m : Fin (D+1), (relativeGramEntry G theta j m -
        (if j = m then ContinuousLinearMap.id ℂ (LLL G theta 4) else 0)) (f m) := by
  classical
  change relativeJetTruncation G theta D ((relativeJetTruncation G theta D).adjoint f) j -
    f j = _
  rw [relativeJetTruncation_gram_coordinate]
  have hentry (m : Fin (D+1)) :
      relativeJet G theta 2 2 j.val ((relativeJet G theta 2 2 m.val).adjoint (f m)) =
        relativeGramEntry G theta j.val m.val (f m) :=
    congrArg (fun A : LLL G theta 4 →L[ℂ] LLL G theta 4 => A (f m))
      (relativeJet_comp_adjoint_eq_entry G theta j m hG)
  simp_rw [hentry, ContinuousLinearMap.sub_apply, Finset.sum_sub_distrib]
  congr 1
  have hi (m : Fin (D+1)) :
      (if j = m then ContinuousLinearMap.id ℂ (LLL G theta 4) else 0) (f m) =
        if j = m then f j else 0 := by
    split_ifs with h
    · subst m; rfl
    · simp
  simp_rw [hi]
  simp

/-- Operator-norm convergence budget for the true JJ†−I on the entire COM family. -/
theorem relativeJetGramErrorOperator_opNorm (G : Geometry) (theta : Twist)
    (D : ℕ) (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G) :
    ‖relativeJetGramErrorOperator G theta D‖ ≤ relativeFrameError D L := by
  classical
  simpa only [Fintype.card_fin, relativeFrameError] using
    operator_matrix_opNorm_le (relativeJetGramErrorOperator G theta D)
      (fun j m : Fin (D+1) => relativeGramEntry G theta j m -
        (if j = m then ContinuousLinearMap.id ℂ (LLL G theta 4) else 0))
      (finiteGramError D L) (finiteGramError_nonneg D L)
      (relativeGramEntry_finite_error_le G theta D L hL1 hL)
      (fun f j => relativeJetGramErrorOperator_coordinate G theta D (hL1.trans hL) f j)

/-- The norm of the true full-COM JJ†−I tends to zero for arbitrary varying
geometries and twists once the actual shortest cycle tends to infinity. -/
theorem relativeJetGramErrorOperator_norm_tendsto {ι : Type*} {l : Filter ι}
    (G : ι → Geometry) (theta : ι → Twist) (D : ℕ)
    (hG : Tendsto (fun a => systole (G a)) l atTop) :
    Tendsto (fun a => ‖relativeJetGramErrorOperator (G a) (theta a) D‖) l (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (relativeFrameError_systole_tendsto G D hG)
  filter_upwards [hG.eventually_ge_atTop 1] with a ha
  exact relativeJetGramErrorOperator_opNorm (G a) (theta a) D (systole (G a)) ha le_rfl

#print axioms relativeJetGramErrorOperator_opNorm
#print axioms relativeJetGramErrorOperator_norm_tendsto

end TorusLean.Shared.RelativeJetFrameAsymptotic
