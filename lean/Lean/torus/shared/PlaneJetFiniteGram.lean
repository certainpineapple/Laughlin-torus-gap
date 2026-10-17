import torus.shared.PlaneJetMixedBounds

set_option autoImplicit false
noncomputable section

namespace TorusLean.Shared.PlaneJetFiniteGram

open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.PlaneJetMixedBounds
open TorusLean.Fermion.LatticePacking
open Filter Topology
open scoped ComplexConjugate

def finiteGramConstant (J : ℕ) : ℝ :=
  ∑ j : Fin (J+1), ∑ m : Fin (J+1), mixedCoefficientEnvelope j m

theorem finiteGramConstant_nonneg (J : ℕ) : 0 ≤ finiteGramConstant J := by
  apply Finset.sum_nonneg
  intro j _
  exact Finset.sum_nonneg fun m _ => mixedCoefficientEnvelope_nonneg j m

theorem mixedCoefficientEnvelope_le_finite (J : ℕ) (j m : Fin (J+1)) :
    mixedCoefficientEnvelope j m ≤ finiteGramConstant J := by
  have h1 : mixedCoefficientEnvelope j m ≤ ∑ k : Fin (J+1), mixedCoefficientEnvelope j k :=
    Finset.single_le_sum (fun k : Fin (J+1) => fun _ => mixedCoefficientEnvelope_nonneg j k) (Finset.mem_univ m)
  have h2 : (∑ k : Fin (J+1), mixedCoefficientEnvelope j k) ≤ finiteGramConstant J :=
    Finset.single_le_sum (fun k : Fin (J+1) => fun _ => Finset.sum_nonneg fun t : Fin (J+1) => fun _ =>
      mixedCoefficientEnvelope_nonneg k t) (Finset.mem_univ j)
  exact h1.trans h2

def finiteGramError (J : ℕ) (L : ℝ) : ℝ :=
  finiteGramConstant J * gaussianConstant * Real.exp (-L^2/8)

theorem finiteGramError_nonneg (J : ℕ) (L : ℝ) : 0 ≤ finiteGramError J L :=
  mul_nonneg (mul_nonneg (finiteGramConstant_nonneg J) gaussianConstant_nonneg)
    (Real.exp_nonneg _)

theorem finite_gram_entry_error (G : Geometry) (theta : Twist) (J : ℕ)
    (R : ℂ) (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G) (j m : Fin (J+1)) :
    ‖inner ℂ (rawPlaneJet G theta j R) (rawPlaneJet G theta m R) -
      (if j = m then (1 : ℂ) else 0)‖ ≤ finiteGramError J L := by
  have h := rawPlaneJet_mixed_gram_error_le G theta j m R L hL1 hL
  have heq : (j.val = m.val) ↔ j = m := Fin.val_inj
  have h' : ‖inner ℂ (rawPlaneJet G theta j R) (rawPlaneJet G theta m R) -
      (if j = m then (1 : ℂ) else 0)‖ ≤
      mixedCoefficientEnvelope j m * gaussianConstant * Real.exp (-L^2/8) := by
    simpa only [heq, lll_inner_eq_cellInner, rawPlaneJet_val] using h
  exact h'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mixedCoefficientEnvelope_le_finite J j m)
      gaussianConstant_nonneg) (Real.exp_nonneg _))

theorem complex_quadratic_norm_le {ι : Type*} [Fintype ι]
    (A : ι → ι → ℂ) (x : ι → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hA : ∀ i k, ‖A i k‖ ≤ E) :
    ‖∑ i, ∑ k, conj (x i) * A i k * x k‖ ≤
      E * (Fintype.card ι : ℝ) * ∑ i, ‖x i‖^2 := by
  have hs : (∑ i, ‖x i‖)^2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖x i‖^2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : ι => (1 : ℝ))
      (fun i => ‖x i‖)
  calc
    _ ≤ ∑ i, ∑ k, ‖conj (x i) * A i k * x k‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ k, ‖x i‖ * E * ‖x k‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, norm_mul, Complex.norm_conj]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hA i k) (norm_nonneg _))
        (norm_nonneg _)
    _ = E * (∑ i, ‖x i‖)^2 := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      ring
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs hE

def jetSynthesis (G : Geometry) (theta : Twist) (J : ℕ) (R : ℂ) (x : Fin (J+1) → ℂ) :
    LLL G theta 1 := ∑ j, x j • rawPlaneJet G theta j R

theorem jetSynthesis_inner_error (G : Geometry) (theta : Twist) (J : ℕ)
    (R : ℂ) (x : Fin (J+1) → ℂ) :
    inner ℂ (jetSynthesis G theta J R x) (jetSynthesis G theta J R x) -
        ((∑ j, ‖x j‖^2 : ℝ) : ℂ) =
      ∑ j : Fin (J+1), ∑ m : Fin (J+1), conj (x j) *
        (inner ℂ (rawPlaneJet G theta j R) (rawPlaneJet G theta m R) -
          (if j = m then (1 : ℂ) else 0)) * x m := by
  classical
  unfold jetSynthesis
  rw [sum_inner]
  simp_rw [inner_sum, inner_smul_left, inner_smul_right]
  simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro m _
    ring
  · simp [Complex.conj_mul', ← Complex.ofReal_pow]

/-- Almost-isometry in the actual cell Hilbert space for every finite
coefficient vector. This controls the complete Gram, including off-diagonal
entries; the coefficient norm is the genuine Euclidean sum of squares. -/
theorem jetSynthesis_norm_sq_error_le (G : Geometry) (theta : Twist) (J : ℕ)
    (R : ℂ) (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G) (x : Fin (J+1) → ℂ) :
    |‖jetSynthesis G theta J R x‖^2 - ∑ j, ‖x j‖^2| ≤
      finiteGramError J L * (J+1 : ℕ) * ∑ j, ‖x j‖^2 := by
  have h := complex_quadratic_norm_le
    (fun j m : Fin (J+1) => inner ℂ (rawPlaneJet G theta j R) (rawPlaneJet G theta m R) -
      (if j = m then (1 : ℂ) else 0)) x (finiteGramError J L)
    (finiteGramError_nonneg J L) (finite_gram_entry_error G theta J R L hL1 hL)
  rw [← jetSynthesis_inner_error] at h
  have hn : ‖jetSynthesis G theta J R x‖^2 =
      (inner ℂ (jetSynthesis G theta J R x) (jetSynthesis G theta J R x)).re :=
    InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) _
  calc
    _ = |(inner ℂ (jetSynthesis G theta J R x) (jetSynthesis G theta J R x) -
        ((∑ j, ‖x j‖^2 : ℝ) : ℂ)).re| := by
      rw [Complex.sub_re, Complex.ofReal_re, ← hn]
    _ ≤ ‖inner ℂ (jetSynthesis G theta J R x) (jetSynthesis G theta J R x) -
        ((∑ j, ‖x j‖^2 : ℝ) : ℂ)‖ := Complex.abs_re_le_norm _
    _ ≤ _ := by simpa only [Fintype.card_fin] using h

theorem jetSynthesis_two_sided (G : Geometry) (theta : Twist) (J : ℕ)
    (R : ℂ) (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G) (x : Fin (J+1) → ℂ) :
    (1 - finiteGramError J L * (J+1 : ℕ)) * (∑ j, ‖x j‖^2) ≤
        ‖jetSynthesis G theta J R x‖^2 ∧
    ‖jetSynthesis G theta J R x‖^2 ≤
        (1 + finiteGramError J L * (J+1 : ℕ)) * (∑ j, ‖x j‖^2) := by
  have h := abs_le.mp (jetSynthesis_norm_sq_error_le G theta J R L hL1 hL x)
  constructor <;> nlinarith [h.1, h.2]

theorem finiteGramError_tendsto (J : ℕ) :
    Tendsto (finiteGramError J) atTop (𝓝 0) := by
  have hs : Tendsto (fun L : ℝ => L^2 / 8) atTop atTop :=
    (tendsto_div_const_atTop_of_pos (by norm_num : (0 : ℝ) < 8)).mpr
      (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))
  change Tendsto (fun L : ℝ => finiteGramConstant J * gaussianConstant * Real.exp (-L^2/8)) atTop (𝓝 0)
  simpa only [Function.comp_def, neg_div, mul_zero] using
    (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hs)).const_mul
      (finiteGramConstant J * gaussianConstant)

theorem finiteGramOperatorError_tendsto (J : ℕ) :
    Tendsto (fun L : ℝ => finiteGramError J L * (J+1 : ℕ)) atTop (𝓝 0) := by
  simpa only [zero_mul] using (finiteGramError_tendsto J).mul_const ((J+1 : ℕ) : ℝ)

#print axioms jetSynthesis_two_sided
#print axioms finiteGramOperatorError_tendsto
#print axioms finiteGramError_tendsto
#print axioms finiteGramConstant_nonneg
#print axioms mixedCoefficientEnvelope_le_finite
#print axioms finiteGramError_nonneg
#print axioms finite_gram_entry_error
#print axioms complex_quadratic_norm_le
#print axioms jetSynthesis_inner_error
#print axioms jetSynthesis_norm_sq_error_le

end TorusLean.Shared.PlaneJetFiniteGram
