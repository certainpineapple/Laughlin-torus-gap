import torus.shared.FermionLocalJetPairBound
import torus.shared.FermionLocalJetDescendantEnergy
import torus.shared.FermionRelativeFrameAllN

/-! The original T4 is bounded by 5152(1+e23)^2 times the same H. The literal
relative C_d, every d=0,...,22, original mu4=2mu2, and all physical sectors are
retained. This extends the existing genuine frame bound rather than changing it. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.FermionRelativeFrame TorusLean.Shared.RelativeJetMap
open TorusLean.Shared.ChargeTwoScaling TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.PhysicalFermionCarrier TorusLean.Shared.PhysicalFermionExterior
open TorusLean.Shared.PhysicalFermionNormalSquare TorusLean.Shared.PhysicalFermionM1Contact
open TorusLean.Shared.FermionM1NearProjectionPhysical TorusLean.Fermion.LatticePacking
open scoped BigOperators

def fourRelativeCoefficient (d p : ℕ) : ℝ :=
  (-1)^(d-p) * Real.sqrt (d.choose p : ℝ) * (scale/2)^d

theorem fourRelativeCoefficient_complex (d p : ℕ) :
    (fourRelativeCoefficient d p : ℂ) = relativeBinomialCoeff d p := by
  unfold fourRelativeCoefficient relativeBinomialCoeff
  push_cast
  rfl

theorem fourRelativeCoefficient_sq (d p : ℕ) :
    (fourRelativeCoefficient d p)^2 = (d.choose p : ℝ) * (1/2 : ℝ)^d := by
  have hpow (a : ℝ) (n : ℕ) : (a^n)^2 = (a^2)^n := by rw [← pow_mul,← pow_mul,Nat.mul_comm n 2]
  have hs : (scale/2 : ℝ)^2 = 1/2 := by rw [div_pow,scale_sq]; norm_num
  unfold fourRelativeCoefficient
  rw [mul_pow,mul_pow,hpow (-1),hpow (scale/2),hs,Real.sq_sqrt (Nat.cast_nonneg _)]
  norm_num

theorem fourRelativeCoefficient_sq_sum (d : ℕ) :
    (∑ p : Fin (d+1), (fourRelativeCoefficient d p.val)^2) = 1 := by
  simp_rw [fourRelativeCoefficient_sq]
  rw [← Finset.sum_mul]
  have hc : (∑ p : Fin (d+1), (d.choose p.val : ℝ)) = 2^d := by
    rw [Fin.sum_univ_eq_sum_range (fun p => (d.choose p : ℝ))]
    exact_mod_cast Nat.sum_range_choose d
  rw [hc,← mul_pow]
  norm_num

/-- The original two-CAR C_d pointwise bound with every relative degree kept. -/
theorem paperFourBodyJet_pointwise_pair_budget (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (d : ℕ) (hd : d ≤ 22) (R : ℂ)
    (x : Space (physicalQ G theta)) :
    occupationNormSq (physicalQ G theta) (paperFourBodyJet G theta d R x) ≤
      (1+e23 G theta)^2 * ∑ p : Fin (d+1), (p.val+2 : ℕ) *
        occupationNormSq (physicalQ G theta) (pairDescendant G theta (d-p.val) R x) := by
  rw [← fourBodyJet_eq_paper]
  simp only [fourBodyJet,LinearMap.sum_apply,LinearMap.smul_apply,Module.End.mul_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun p => relativeBinomialCoeff d p •
    pairDescendant G theta p R (pairDescendant G theta (d-p) R x)) (d+1)]
  simp_rw [← fourRelativeCoefficient_complex]
  apply (normalized_occupation_sum_bound (physicalQ G theta)
    (fun p : Fin (d+1) => fourRelativeCoefficient d p.val)
    (fun p => pairDescendant G theta p.val R (pairDescendant G theta (d-p.val) R x))
    (fourRelativeCoefficient_sq_sum d)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  have h := pairDescendant_left_factor G theta hG p.val (by have := p.isLt; omega) R
    (pairDescendant G theta (d-p.val) R x)
  nlinarith

/-- Exact original normalization, for arbitrary scalar integrands. -/
theorem cellIntegral_four_eq_two (G : Geometry) (f : ℂ → ℝ) :
    (∫ R, f R ∂cellMeasure G 4) = 2 * ∫ R, f R ∂cellMeasure G 2 := by
  unfold cellMeasure
  rw [integral_smul_measure,integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity),ENNReal.toReal_ofReal (by positivity)]
  simp only [smul_eq_mul]
  ring

theorem four_left_factor_count :
    2 * (∑ d : Fin 23, ∑ p : Fin (d.val+1), (p.val+2)) = 5152 := by decide +kernel

set_option maxHeartbeats 800000 in
/-- Same original H, all physical N, with the manuscript constant 5152. -/
theorem physicalFourJetEnergyAll_same_H_bound (G : Geometry) (theta : Twist)
    (hG : 1 ≤ systole G) (N : ℕ) (f : PhysicalFermion G theta N) :
    physicalFourJetEnergyAll G theta N 22 f ≤
      5152 * (1+e23 G theta)^2 * actualFermionM1Energy G N f.val := by
  let x := (physicalExteriorEquiv G theta N).symm f
  let E := (occupationInner (physicalQ G theta) (x : Space (physicalQ G theta))
    (physicalHamiltonian G theta x)).re
  let P : ℂ → ℝ := fun R => ∑ d : Fin 23, ∑ p : Fin (d.val+1), (p.val+2 : ℕ) *
    occupationNormSq (physicalQ G theta) (pairDescendant G theta (d.val-p.val) R x)
  have hi (d : Fin 23) (p : Fin (d.val+1)) (k : ℕ) : Integrable (fun R =>
      (p.val+2 : ℕ) * occupationNormSq (physicalQ G theta)
        (pairDescendant G theta (d.val-p.val) R x)) (cellMeasure G k) :=
    continuous_integrable_cellMeasure G k
      ((pairDescendant_occupation_continuous G theta x _).const_mul _)
  have hP (k : ℕ) : Integrable P (cellMeasure G k) :=
    integrable_finsetSum _ (fun d hd => integrable_finsetSum _ (fun p hp => hi d p k))
  have he : 2 * (∫ R, P R ∂cellMeasure G 2) = 5152 * E := by
    change 2 * (∫ R, ∑ d : Fin 23, _ ∂cellMeasure G 2) = _
    rw [integral_finsetSum _ (fun d hd => integrable_finsetSum _ (fun p hp => hi d p 2))]
    simp_rw [integral_finsetSum _ (fun p hp => hi _ p 2),integral_const_mul,pairDescendant_same_H_energy]
    change 2 * (∑ d : Fin 23, ∑ p : Fin (d.val+1), (p.val+2 : ℕ) * E) = _
    simp_rw [← Finset.sum_mul]
    have hc : (2 : ℝ) * (∑ d : Fin 23, ∑ p : Fin (d.val+1), (p.val+2 : ℕ)) = 5152 := by
      exact_mod_cast four_left_factor_count
    simp only [Nat.cast_sum] at hc
    rw [← mul_assoc,hc]
  rw [← physicalHamiltonian_actual_energy G theta N f]
  change (∫ R, ∑ d : Fin 23, occupationNormSq (physicalQ G theta)
    (paperFourBodyJet G theta d.val R x) ∂cellMeasure G 4) ≤ 5152 * (1+e23 G theta)^2 * E
  calc
    _ ≤ ∫ R, (1+e23 G theta)^2 * P R ∂cellMeasure G 4 := by
      apply integral_mono
        (integrable_finsetSum _ (fun (d : Fin 23) _ =>
          paperFourBodyJet_normSq_integrable_all G theta N d.val x))
        ((hP 4).const_mul _)
      intro R
      dsimp only [P]
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun d hd => paperFourBodyJet_pointwise_pair_budget G theta hG
        d.val (by have := d.isLt; omega) R x
    _ = _ := by
      rw [integral_const_mul,cellIntegral_four_eq_two,he]
      ring

/-- The genuine full-COM S4/T4 frame error is now paid by the same H. -/
theorem four_frame_same_H_payment_threshold (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (G : Geometry) (theta : Twist), L ≤ systole G →
      ∀ (N : ℕ) (f : PhysicalFermion G theta N),
        physicalFourJetEnergyAll G theta N 22 f -
          5152 * (1+e23 G theta)^2 * ε * actualFermionM1Energy G N f.val ≤
        (occupationInner (physicalQ G theta)
          ((physicalExteriorEquiv G theta N).symm f : Space (physicalQ G theta))
          (matrixFourBody (physicalQ G theta) (contactMatrix G theta)
            ((physicalExteriorEquiv G theta N).symm f : Space (physicalQ G theta)))).re := by
  obtain ⟨L,hL1,hL⟩ := physicalFourJetEnergyAll_degree22_exists_threshold ε hε
  refine ⟨L,hL1,fun G theta hG N f => ?_⟩
  have hframe := hL G theta hG N f
  have hpay := physicalFourJetEnergyAll_same_H_bound G theta (hL1.trans hG) N f
  have hT : 0 ≤ physicalFourJetEnergyAll G theta N 22 f :=
    integral_nonneg (fun R => Finset.sum_nonneg fun d hd => occupationNormSq_nonneg _ _)
  let S := (occupationInner (physicalQ G theta)
    ((physicalExteriorEquiv G theta N).symm f : Space (physicalQ G theta))
    (matrixFourBody (physicalQ G theta) (contactMatrix G theta)
      ((physicalExteriorEquiv G theta N).symm f : Space (physicalQ G theta)))).re
  change physicalFourJetEnergyAll G theta N 22 f ≤ (1+ε)*S at hframe
  change _ ≤ S
  have hp := mul_le_mul_of_nonneg_left hpay hε.le
  by_cases hs : physicalFourJetEnergyAll G theta N 22 f ≤ S
  · have hn := mul_nonneg hε.le (hT.trans hpay)
    nlinarith
  · have hs' : S ≤ physicalFourJetEnergyAll G theta N 22 f := (not_le.mp hs).le
    have hmul := mul_le_mul_of_nonneg_left hs' hε.le
    nlinarith

/-- A single geometry/twist/particle independent threshold pays the genuine
four-body frame discrepancy with any prescribed same-H relative error. -/
theorem four_frame_uniform_same_H_threshold (δ : ℝ) (hδ : 0 < δ) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ (G : Geometry) (theta : Twist), L ≤ systole G →
      ∀ (N : ℕ) (f : PhysicalFermion G theta N),
        physicalFourJetEnergyAll G theta N 22 f - δ * actualFermionM1Energy G N f.val ≤
        (occupationInner (physicalQ G theta)
          ((physicalExteriorEquiv G theta N).symm f : Space (physicalQ G theta))
          (matrixFourBody (physicalQ G theta) (contactMatrix G theta)
            ((physicalExteriorEquiv G theta N).symm f : Space (physicalQ G theta)))).re := by
  obtain ⟨LF,hF1,hF⟩ := four_frame_same_H_payment_threshold (δ/20608) (by positivity)
  obtain ⟨L23,h231,h23⟩ := localJetError_exists_threshold 23 1 (by norm_num)
  refine ⟨max LF L23,hF1.trans (le_max_left _ _),fun G theta hG N f => ?_⟩
  have hg : 1 ≤ systole G := hF1.trans ((le_max_left _ _).trans hG)
  have he : 0 ≤ e23 G theta := localJetError_nonneg G theta 23 hg
  have he1 : e23 G theta ≤ 1 := h23 G theta ((le_max_right _ _).trans hG)
  have hs : (1+e23 G theta)^2 ≤ 4 := by
    have h := pow_le_pow_left₀ (show 0 ≤ 1+e23 G theta by linarith)
      (show 1+e23 G theta ≤ 2 by linarith) 2
    norm_num at h
    exact h
  have hc : 5152*(1+e23 G theta)^2*(δ/20608) ≤ δ := by
    have hm := mul_le_mul_of_nonneg_right hs (show 0 ≤ δ/20608 by positivity)
    nlinarith
  have hE : 0 ≤ actualFermionM1Energy G N f.val := by
    rw [← physicalHamiltonian_actual_energy G theta N f]
    exact physicalHamiltonian_nonneg G theta _
  have hp := hF G theta ((le_max_left _ _).trans hG) N f
  have hm := mul_le_mul_of_nonneg_right hc hE
  linarith

#print axioms fourRelativeCoefficient_complex
#print axioms fourRelativeCoefficient_sq
#print axioms fourRelativeCoefficient_sq_sum
#print axioms paperFourBodyJet_pointwise_pair_budget
#print axioms cellIntegral_four_eq_two
#print axioms four_left_factor_count
#print axioms physicalFourJetEnergyAll_same_H_bound
#print axioms four_frame_same_H_payment_threshold
#print axioms four_frame_uniform_same_H_threshold
end TorusLean.Shared.FermionLocalJet
