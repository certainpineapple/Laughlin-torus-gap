import torus.shared.ParameterRawJetLadderActions
import torus.shared.ParameterLadderProduct

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ParameterRawJetWord
open TorusLean.Geometry TorusLean.Shared.ParameterCellAdjoint
open TorusLean.Shared.ParameterRawJetLadder TorusLean.Shared.ParameterLadderProduct
open scoped ComplexConjugate BigOperators ContDiff

theorem wirtinger_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) (R : ℂ) :
    parameterWirtinger (fun z => ∏ i ∈ s, f i z) R =
      ∑ i ∈ s, (∏ j ∈ s.erase i, f j R) * parameterWirtinger (f i) R := by
  unfold parameterWirtinger
  rw [fderiv_finsetProd (fun i hi => hf i hi R)]
  simp only [sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem wirtingerBar_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) (R : ℂ) :
    parameterWirtingerBar (fun z => ∏ i ∈ s, f i z) R =
      ∑ i ∈ s, (∏ j ∈ s.erase i, f j R) * parameterWirtingerBar (f i) R := by
  unfold parameterWirtingerBar
  rw [fderiv_finsetProd (fun i hi => hf i hi R)]
  simp only [sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- A product of charge-one parameter factors has the physical COM scale sqrt(k). -/
theorem parameterLower_prod (k : ℕ) [NeZero k] (f : Fin k → ℂ → ℂ)
    (hf : ∀ i, Differentiable ℝ (f i)) (R : ℂ) :
    (Real.sqrt (k:ℝ):ℂ) * parameterLower k (fun z => ∏ i, f i z) R =
      ∑ i, (∏ l ∈ Finset.univ.erase i, f l R) * parameterLower 1 (f i) R := by
  classical
  have hk : (Real.sqrt (k:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k)))))
  have hp (i : Fin k) : (∏ l ∈ Finset.univ.erase i, f l R)*f i R = ∏ l, f l R :=
    Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  unfold parameterLower
  rw [wirtinger_prod _ _ (fun i _ => hf i) R]
  simp only [Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, div_one]
  rw [mul_div_cancel₀ _ hk]
  simp_rw [mul_neg, mul_add]
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib]
  congr 1
  congr 1
  calc
    _ = ∑ i : Fin k, (1/2:ℂ)*conj R*(∏ l, f l R) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show (∏ l ∈ Finset.univ.erase i, f l R)*((1/2:ℂ)*conj R*f i R) =
        (1/2:ℂ)*conj R*((∏ l ∈ Finset.univ.erase i, f l R)*f i R) by ring, hp]

theorem parameterRaise_prod (k : ℕ) [NeZero k] (f : Fin k → ℂ → ℂ)
    (hf : ∀ i, Differentiable ℝ (f i)) (R : ℂ) :
    (Real.sqrt (k:ℝ):ℂ) * parameterRaise k (fun z => ∏ i, f i z) R =
      ∑ i, (∏ l ∈ Finset.univ.erase i, f l R) * parameterRaise 1 (f i) R := by
  classical
  have hk : (Real.sqrt (k:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k)))))
  have hp (i : Fin k) : (∏ l ∈ Finset.univ.erase i, f l R)*f i R = ∏ l, f l R :=
    Finset.prod_erase_mul _ _ (Finset.mem_univ i)
  unfold parameterRaise
  rw [wirtingerBar_prod _ _ (fun i _ => hf i) R]
  simp only [Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, div_one]
  rw [mul_div_cancel₀ _ hk]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  calc
    _ = ∑ i : Fin k, (1/2:ℂ)*R*(∏ l, f l R) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show (∏ l ∈ Finset.univ.erase i, f l R)*((1/2:ℂ)*R*f i R) =
        (1/2:ℂ)*R*((∏ l ∈ Finset.univ.erase i, f l R)*f i R) by ring, hp]

theorem hasDualBoundary_prod {ι : Type*} [DecidableEq ι] (G : Geometry) (theta : Twist)
    (s : Finset ι) (f : ι → ℂ → ℂ) (hf : ∀ i ∈ s, HasDualBoundary G theta 1 (f i)) :
    HasDualBoundary G theta s.card (fun z => ∏ i ∈ s, f i z) := by
  induction s using Finset.induction_on with
  | empty =>
    intro p
    funext z
    simp [magneticTranslate, magneticExponent]
  | @insert i s hi ih =>
    have hh := hasDualBoundary_mul G theta 1 s.card (f i) (fun z => ∏ l ∈ s, f l z)
      (hf i (Finset.mem_insert_self _ _)) (ih (fun l hl => hf l (Finset.mem_insert_of_mem hl)))
    simpa only [Finset.card_insert_of_notMem hi, Finset.prod_insert hi, Nat.add_comm] using hh

/-- Actual tensor-coordinate products of the original raw physical jets. -/
def rawWord (G : Geometry) (theta : Twist) (k : ℕ)
    (h : Fin k → LLL G theta 1) (j : Fin k → ℕ) (R : ℂ) : ℂ :=
  ∏ i, dualRawJetScalar G theta (h i) (j i) R

theorem rawWord_contDiff (G : Geometry) (theta : Twist) (k : ℕ)
    (h : Fin k → LLL G theta 1) (j : Fin k → ℕ) : ContDiff ℝ ∞ (rawWord G theta k h j) := by
  have H (s : Finset (Fin k)) : ContDiff ℝ ∞ (fun R => ∏ i ∈ s, dualRawJetScalar G theta (h i) (j i) R) := by
    induction s using Finset.induction_on with
    | empty => simpa using (contDiff_const : ContDiff ℝ ∞ (fun _ : ℂ => (1:ℂ)))
    | @insert i s hi ih =>
      simpa only [Finset.prod_insert hi] using (dualRawJetScalar_contDiff G theta (h i) (j i)).mul ih
  exact H Finset.univ

theorem rawWord_hasDualBoundary (G : Geometry) (theta : Twist) (k : ℕ)
    (h : Fin k → LLL G theta 1) (j : Fin k → ℕ) :
    HasDualBoundary G theta k (rawWord G theta k h j) := by
  change HasDualBoundary G theta k (fun R => ∏ i, dualRawJetScalar G theta (h i) (j i) R)
  simpa only [Finset.card_univ, Fintype.card_fin] using
    hasDualBoundary_prod G theta Finset.univ (fun i => dualRawJetScalar G theta (h i) (j i))
      (fun i _ => dualRawJetScalar_hasDualBoundary G theta (h i) (j i))

theorem dualRawJetScalar_lower_all (G : Geometry) (theta : Twist) (h : LLL G theta 1) (j : ℕ) :
    parameterLower 1 (dualRawJetScalar G theta h j) =
      (Real.sqrt (j:ℝ):ℂ) • dualRawJetScalar G theta h (j-1) := by
  cases j with
  | zero => simp [dualRawJetScalar_lower_zero]
  | succ j => simpa using dualRawJetScalar_lower_succ G theta h j

theorem rawWord_lower (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (h : Fin k → LLL G theta 1) (j : Fin k → ℕ) (R : ℂ) :
    (Real.sqrt (k:ℝ):ℂ)*parameterLower k (rawWord G theta k h j) R =
      ∑ i, (Real.sqrt (j i:ℝ):ℂ) * (∏ l ∈ Finset.univ.erase i, dualRawJetScalar G theta (h l) (j l) R) *
        dualRawJetScalar G theta (h i) (j i-1) R := by
  unfold rawWord
  rw [parameterLower_prod k _ (fun i => (dualRawJetScalar_contDiff G theta (h i) (j i)).differentiable (by simp))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dualRawJetScalar_lower_all]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem rawWord_raise (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (h : Fin k → LLL G theta 1) (j : Fin k → ℕ) (R : ℂ) :
    (Real.sqrt (k:ℝ):ℂ)*parameterRaise k (rawWord G theta k h j) R =
      ∑ i, (Real.sqrt ((j i+1:ℕ):ℝ):ℂ) * (∏ l ∈ Finset.univ.erase i, dualRawJetScalar G theta (h l) (j l) R) *
        dualRawJetScalar G theta (h i) (j i+1) R := by
  unfold rawWord
  rw [parameterRaise_prod k _ (fun i => (dualRawJetScalar_contDiff G theta (h i) (j i)).differentiable (by simp))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [dualRawJetScalar_raise]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

#print axioms rawWord_lower
#print axioms rawWord_raise
#print axioms rawWord_hasDualBoundary

end TorusLean.Shared.ParameterRawJetWord
