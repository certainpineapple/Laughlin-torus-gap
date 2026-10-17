import torus.shared.ThermalCoherentFermionAnchoredJacobiAnchoredColumns

/-! Absolute exchange in the original outer mu2 cell. The only majorants
are used to prove convergence for the given whole-Fock vectors x,y. They
are never inserted into a physical energy estimate. Every physical L1
premise is filled from the genuine finite section expansion. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiOuterExchange
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalFermionNormalSquare
open TorusLean.Shared.PlaneJetReproducing TorusLean.Shared.ParameterRawJetLadder
open TorusLean.Shared.RelativeJetMap TorusLean.Shared.ChargeTwoScaling
open TorusLean.Shared.ChargeTwoIsometry TorusLean.Fermion.LatticePacking
open TorusLean.Shared.BosonAnchoredCoefficientGrowth
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiPairGenerating
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiAnchoredColumns
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiOneEdge
open scoped BigOperators ComplexConjugate

private theorem pair_evaluation_continuous (G : Geometry) (theta : Twist)
    (f : LLL G theta 2) (p : ℕ) :
    Continuous (fun R => chargeTwoJetEvaluation G theta p R f) := by
  change Continuous (fun R => rawJetCoefficient (scaledGeometry G) (scaledTwist theta)
    ((scalingLinearIsometryEquiv G theta).symm f) p ((scale:ℂ)*R))
  exact (rawJetCoefficient_contDiff _ _ _ _).continuous.comp
    (continuous_const.mul continuous_id)

/-- The p-independent coefficient is a genuine finite scalar sum. No norm
or topology on the raw exterior algebra is needed for its continuity. -/
theorem sectionConstant_continuous (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (k : ℕ)
    (i : ModeIndex G theta) (a : PairIndex G theta) :
    Continuous (fun R => sectionConstant G theta x y k R i a) := by
  have he (R : ℂ) : sectionConstant G theta x y k R i a =
      ∑ b : PairIndex G theta, ∑ m : ModeIndex G theta,
        conj ((TorusLean.Shared.FermionRelativeFrame.pairSection G theta b).val R) *
        rawJetCoefficient G theta (modeSection G theta m) k R *
        occupationInner (physicalQ G theta)
          (annihilate i (modePairAnnihilate (physicalQ G theta) b x))
          (annihilate m (modePairAnnihilate (physicalQ G theta) a y)) := by
    classical
    unfold sectionConstant
    rw [TorusLean.Shared.FermionRelativeFrame.pairAt_section_expansion,
      vectorAnnihilate_sum]
    simp only [LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,
      physicalJetCoordinates_star,occupationInner_sum_left,occupationInner_sum_right,
      occupationInner_smul_left,occupationInner_smul_right,Complex.star_def,modeSection,
      Finset.mul_sum,mul_assoc]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro m hm
    ring
  simp_rw [he]
  apply continuous_finset_sum
  intro b _
  apply continuous_finset_sum
  intro m _
  exact (((rawLLL_continuous G theta 2
    (TorusLean.Shared.FermionRelativeFrame.pairSection G theta b)).star.mul
      (rawJetCoefficient_contDiff G theta (modeSection G theta m) k).continuous).mul
        continuous_const)

theorem anchoredCross_continuous (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (j k p : ℕ) :
    Continuous (anchoredCross G theta x y j k p) := by
  classical
  change Continuous (fun R => anchoredCross G theta x y j k p R)
  simp_rw [anchoredCross_section_expansion]
  apply continuous_finset_sum
  intro i _
  apply continuous_finset_sum
  intro a _
  exact (((rawJetCoefficient_contDiff G theta (modeSection G theta i) j).continuous.star.mul
    (pair_evaluation_continuous G theta
      (TorusLean.Shared.FermionRelativeFrame.pairSection G theta a) p)).mul
        (sectionConstant_continuous G theta x y k i a))

private theorem polynomial_decay_summable :
    Summable (fun p : ℕ => ((p:ℝ)+1)^3*(Real.sqrt (2:ℝ))⁻¹^p) := by
  let r : ℝ := (Real.sqrt (2:ℝ))⁻¹
  have hs : 1<Real.sqrt (2:ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg (2:ℝ)]
  have hr0 : 0<r := by dsimp [r]; positivity
  have hr1 : r<1 := by dsimp [r]; exact inv_lt_one_of_one_lt₀ hs
  have ht := summable_pow_mul_geometric_of_norm_lt_one 3
    (show ‖r‖<1 by simpa only [Real.norm_eq_abs,abs_of_pos hr0] using hr1)
  have hu : Summable (fun p : ℕ => ((p+1:ℕ):ℝ)^3*r^(p+1)) :=
    (summable_nat_add_iff 1).mpr ht
  have hv := hu.mul_left r⁻¹
  convert hv using 1
  funext p
  simp only [Nat.cast_add,Nat.cast_one,pow_succ]
  change ((p:ℝ)+1)^3*r^p = _
  field_simp [ne_of_gt hr0]

private theorem weighted_scalar_integrable (G : Geometry) (theta : Twist)
    (h : LLL G theta 1) (f : LLL G theta 2) (C : ℂ → ℂ) (hC : Continuous C)
    (j p : ℕ) (w : ℂ) :
    Integrable (fun R => w*conj (rawJetCoefficient G theta h j R)*
      chargeTwoJetEvaluation G theta p R f*C R) (cellMeasure G 2) :=
  continuous_integrable_cellMeasure G 2
    (((continuous_const.mul (rawJetCoefficient_contDiff G theta h j).continuous.star).mul
      (pair_evaluation_continuous G theta f p)).mul hC)

private theorem weighted_scalar_absolute (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (h : LLL G theta 1) (f : LLL G theta 2)
    (C : ℂ → ℂ) (hC : Continuous C) (J : ℕ → ℕ) (w : ℕ → ℂ)
    (hJ : ∀ p, J p≤p+1)
    (hw : ∀ p, ‖w p‖≤((p:ℝ)+1)*(Real.sqrt (2:ℝ))⁻¹^p) :
    Summable (fun p => ∫ R,
      ‖w p*conj (rawJetCoefficient G theta h (J p) R)*
        chargeTwoJetEvaluation G theta p R f*C R‖ ∂cellMeasure G 2) := by
  let Ch : ℝ := (4096+gaussianConstant)*‖h‖
  let Cf : ℝ := (4096+gaussianConstant)*‖f‖
  have hGC : 0≤4096+gaussianConstant := by linarith [gaussianConstant_nonneg]
  have hCh : 0≤Ch := by dsimp [Ch]; positivity
  have hCf : 0≤Cf := by dsimp [Cf]; positivity
  have hiC := (continuous_integrable_cellMeasure G 2 hC).norm
  have hb (p : ℕ) (R : ℂ) :
      ‖w p*conj (rawJetCoefficient G theta h (J p) R)*
        chargeTwoJetEvaluation G theta p R f*C R‖ ≤
      (2*Ch*Cf)*(((p:ℝ)+1)^3*(Real.sqrt (2:ℝ))⁻¹^p)*‖C R‖ := by
    have hA : ‖rawJetCoefficient G theta h (J p) R‖≤2*Ch*((p:ℝ)+1) := by
      apply (rawJetCoefficient_norm_le G theta hG h (J p) R).trans
      have hj : (J p:ℝ)+1≤2*((p:ℝ)+1) := by
        have hc : (J p:ℝ)≤(p:ℝ)+1 := by exact_mod_cast hJ p
        have hp : 0≤(p:ℝ) := Nat.cast_nonneg p
        linarith
      change Ch*((J p:ℝ)+1)≤_
      nlinarith [mul_le_mul_of_nonneg_left hj hCh]
    have hB := chargeTwoJetEvaluation_norm_le G theta hG f p R
    rw [norm_mul,norm_mul,norm_mul,Complex.norm_conj]
    calc
      _ ≤ (((p:ℝ)+1)*(Real.sqrt (2:ℝ))⁻¹^p)*
          (2*Ch*((p:ℝ)+1))*(Cf*((p:ℝ)+1))*‖C R‖ := by
        gcongr
        exact hw p
      _ = _ := by ring
  have hs := polynomial_decay_summable.mul_left
    ((2*Ch*Cf)*(∫ R, ‖C R‖ ∂cellMeasure G 2))
  apply Summable.of_nonneg_of_le (fun p => integral_nonneg (fun R => norm_nonneg _)) _ hs
  intro p
  have hh := integral_mono
    (weighted_scalar_integrable G theta h f C hC (J p) p (w p)).norm
    (hiC.const_mul ((2*Ch*Cf)*(((p:ℝ)+1)^3*(Real.sqrt (2:ℝ))⁻¹^p))) (hb p)
  rw [integral_const_mul] at hh
  convert hh using 1 <;> ring

private theorem finite_absolute {ι : Type*} [Fintype ι]
    (G : Geometry) (F : ι → ℕ → ℂ → ℂ)
    (hi : ∀ i p, Integrable (F i p) (cellMeasure G 2))
    (hs : ∀ i, Summable (fun p => ∫ R, ‖F i p R‖ ∂cellMeasure G 2)) :
    Summable (fun p => ∫ R, ‖∑ i, F i p R‖ ∂cellMeasure G 2) := by
  classical
  have hm := (hasSum_sum (s := (Finset.univ : Finset ι))
    (fun i _ => (hs i).hasSum)).summable
  apply Summable.of_nonneg_of_le (fun p => integral_nonneg (fun R => norm_nonneg _)) _ hm
  intro p
  have hh := integral_mono (integrable_finsetSum Finset.univ (fun i _ => hi i p)).norm
    (integrable_finsetSum Finset.univ (fun i _ => (hi i p).norm))
    (fun R => norm_sum_le Finset.univ (fun i => F i p R))
  simpa only [integral_finsetSum Finset.univ (fun i _ => (hi i p).norm)] using hh

private theorem weighted_cross_absolute (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (x y : Space (physicalQ G theta))
    (k : ℕ) (J : ℕ → ℕ) (w : ℕ → ℂ) (hJ : ∀ p, J p≤p+1)
    (hw : ∀ p, ‖w p‖≤((p:ℝ)+1)*(Real.sqrt (2:ℝ))⁻¹^p) :
    Summable (fun p => ∫ R, ‖w p*anchoredCross G theta x y (J p) k p R‖
      ∂cellMeasure G 2) := by
  classical
  let F := fun (i : ModeIndex G theta) (a : PairIndex G theta) (p : ℕ) (R : ℂ) =>
    w p*conj (rawJetCoefficient G theta (modeSection G theta i) (J p) R)*
      chargeTwoJetEvaluation G theta p R
        (TorusLean.Shared.FermionRelativeFrame.pairSection G theta a)*
      sectionConstant G theta x y k R i a
  have hi (i : ModeIndex G theta) (a : PairIndex G theta) (p : ℕ) :
      Integrable (F i a p) (cellMeasure G 2) :=
    weighted_scalar_integrable G theta _ _ _
      (sectionConstant_continuous G theta x y k i a) _ _ _
  have hs (i : ModeIndex G theta) := finite_absolute G (F i) (hi i)
    (fun a => weighted_scalar_absolute G theta hG _ _ _
      (sectionConstant_continuous G theta x y k i a) J w hJ hw)
  have ht := finite_absolute G (fun i p R => ∑ a, F i a p R)
    (fun i p => integrable_finsetSum _ (fun a _ => hi i a p)) hs
  convert ht using 1
  funext p
  apply integral_congr_ae
  filter_upwards [] with R
  simp only [anchoredCross_section_expansion,Finset.mul_sum,F,mul_assoc]

/-- The unchanged two-column physical slice, with p=l-1 in its first term. -/
def originalColumnTerm (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (p : ℕ) (R : ℂ) : ℂ :=
  -((Real.sqrt (p+1:ℝ):ℂ)/(Real.sqrt (2:ℝ):ℂ)^p *
    anchoredCross G theta x y (p+1) 1 p R) +
  ((p:ℂ)-1)/(Real.sqrt (2:ℝ):ℂ)^p*anchoredCross G theta x y p 0 p R

theorem originalColumnTerm_integrable (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (p : ℕ) :
    Integrable (originalColumnTerm G theta x y p) (cellMeasure G 2) :=
  continuous_integrable_cellMeasure G 2
    ((continuous_const.mul (anchoredCross_continuous G theta x y (p+1) 1 p)).neg.add
      (continuous_const.mul (anchoredCross_continuous G theta x y p 0 p)))

/-- Each physical column is absolutely integrable separately. This is
needed for the genuine p=l-1 reindexing, not merely cancellation of their sum. -/
theorem originalColumns_individually_absolute (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (x y : Space (physicalQ G theta)) :
    Summable (fun p : ℕ => ∫ R, ‖(Real.sqrt (p+1:ℝ):ℂ)/(Real.sqrt (2:ℝ):ℂ)^p*
      anchoredCross G theta x y (p+1) 1 p R‖ ∂cellMeasure G 2) ∧
    Summable (fun p : ℕ => ∫ R, ‖((p:ℂ)-1)/(Real.sqrt (2:ℝ):ℂ)^p*
      anchoredCross G theta x y p 0 p R‖ ∂cellMeasure G 2) := by
  have hw0 (p : ℕ) :
      ‖(Real.sqrt (p+1:ℝ):ℂ)/(Real.sqrt (2:ℝ):ℂ)^p‖≤
        ((p:ℝ)+1)*(Real.sqrt (2:ℝ))⁻¹^p := by
    rw [norm_div,norm_pow]
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [div_eq_mul_inv,inv_pow]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply Real.sqrt_le_self_iff.mpr
    right
    have hp : 0≤(p:ℝ) := Nat.cast_nonneg p
    linarith
  have hw1 (p : ℕ) : ‖((p:ℂ)-1)/(Real.sqrt (2:ℝ):ℂ)^p‖≤
      ((p:ℝ)+1)*(Real.sqrt (2:ℝ))⁻¹^p := by
    rw [norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),div_eq_mul_inv,inv_pow]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact (norm_sub_le _ _).trans_eq (by simp)
  have h0 := weighted_cross_absolute G theta hG x y 1 (fun p => p+1)
    (fun p => (Real.sqrt (p+1:ℝ):ℂ)/(Real.sqrt (2:ℝ):ℂ)^p) (fun p => le_rfl) hw0
  have h1 := weighted_cross_absolute G theta hG x y 0 id
    (fun p => ((p:ℂ)-1)/(Real.sqrt (2:ℝ):ℂ)^p) (fun p => Nat.le_succ p) hw1
  exact ⟨h0,h1⟩

/-- Actual absolute L1 convergence in the original outer cell. No N factor
enters an energy budget: the finite x,y-dependent scalar integral appears
only inside this convergence proof. -/
theorem originalColumnTerm_summable_integral_norm (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (x y : Space (physicalQ G theta)) :
    Summable (fun p => ∫ R, ‖originalColumnTerm G theta x y p R‖ ∂cellMeasure G 2) := by
  obtain ⟨h0,h1⟩ := originalColumns_individually_absolute G theta hG x y
  have hi0 (p : ℕ) : Integrable (fun R =>
      (Real.sqrt (p+1:ℝ):ℂ)/(Real.sqrt (2:ℝ):ℂ)^p*
        anchoredCross G theta x y (p+1) 1 p R) (cellMeasure G 2) :=
    continuous_integrable_cellMeasure G 2
      (continuous_const.mul (anchoredCross_continuous G theta x y (p+1) 1 p))
  have hi1 (p : ℕ) : Integrable (fun R =>
      ((p:ℂ)-1)/(Real.sqrt (2:ℝ):ℂ)^p*anchoredCross G theta x y p 0 p R)
        (cellMeasure G 2) :=
    continuous_integrable_cellMeasure G 2
      (continuous_const.mul (anchoredCross_continuous G theta x y p 0 p))
  apply Summable.of_nonneg_of_le (fun p => integral_nonneg (fun R => norm_nonneg _)) _ (h0.add h1)
  intro p
  have hh := integral_mono (originalColumnTerm_integrable G theta x y p).norm
    ((hi0 p).norm.add (hi1 p).norm) (fun R => by
      simpa only [originalColumnTerm,Pi.add_apply,norm_neg] using norm_add_le
        (-((Real.sqrt (p+1:ℝ):ℂ)/(Real.sqrt (2:ℝ):ℂ)^p*
          anchoredCross G theta x y (p+1) 1 p R))
        (((p:ℂ)-1)/(Real.sqrt (2:ℝ):ℂ)^p*anchoredCross G theta x y p 0 p R))
  simp only [Pi.add_apply] at hh
  rw [integral_add (hi0 p).norm (hi1 p).norm] at hh
  exact hh

/-- The original physical S3 operator has the two-column integrated series.
The theorem is proved from the actual four-sign source through one-edge
unfolding and absolute outer exchange; no finite K identity is a premise. -/
theorem matrixSingleContraction_original_columns_hasSum (G : Geometry) (theta : Twist)
    (hG : 1≤systole G) (x y : Space (physicalQ G theta)) :
    HasSum (fun p => ∫ R, originalColumnTerm G theta x y p R ∂cellMeasure G 2)
      (occupationInner (physicalQ G theta) x
        (matrixSingleContraction (physicalQ G theta) (contactMatrix G theta) y)) := by
  have hs := hasSum_integral_of_summable_integral_norm
    (originalColumnTerm_integrable G theta x y)
    (originalColumnTerm_summable_integral_norm G theta hG x y)
  have he (R : ℂ) : (∑' p, originalColumnTerm G theta x y p R)=_ :=
    (original_anchored_columns_slice_hasSum G theta hG x y R).tsum_eq
  simp_rw [he] at hs
  rw [integral_const_mul,← matrixSingleContraction_one_edge_integral] at hs
  exact hs

end TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiOuterExchange
