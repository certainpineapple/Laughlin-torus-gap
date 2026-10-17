import torus.shared.BosonRelativeFrameTensor
import torus.shared.RelativeJetMapOscillator
import torus.shared.BosonLiftSquare
import torus.shared.ChargeTwoEvaluation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonRelativeFrame
open MeasureTheory TorusLean.Geometry TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.PhysicalBosonContactForm
open TorusLean.Shared.PhysicalBosonDiagonal TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Shared.RelativeJetMap TorusLean.Shared.ChargeTwoScaling
open TorusLean.Shared.PlaneJetReproducing TorusLean.Shared.GroundJetReproducing
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.ChargeTwoEvaluation
open scoped TensorProduct ComplexConjugate BigOperators

local instance jetsOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (PhysicalBosonSector.OrbitalIndex G theta) :=
  ⟨⟨0, lll_finrank_pos G theta 1⟩⟩

/-- The positive COM-binomial coefficient, distinct from the signed
relative-binomial coefficient of J_d. -/
def pairDescendantCoeff (d i : ℕ) : ℂ :=
  (Real.sqrt (d.choose i : ℝ) : ℂ) * ((scale : ℂ)/2)^d

theorem normalized_com_leibniz (d : ℕ) (F H : ℂ → ℂ)
    (hF : Differentiable ℂ F) (hH : Differentiable ℂ H) :
    iteratedDeriv d (fun r => F (((scale:ℂ)/2)*r) * H (((scale:ℂ)/2)*r)) 0 /
      (Real.sqrt (d.factorial : ℝ) : ℂ) =
    ∑ i ∈ Finset.range (d+1), pairDescendantCoeff d i *
      (iteratedDeriv i F 0 / (Real.sqrt (i.factorial : ℝ) : ℂ)) *
      (iteratedDeriv (d-i) H 0 / (Real.sqrt ((d-i).factorial : ℝ) : ℂ)) := by
  let c : ℂ := (scale:ℂ)/2
  have hF' (n : ℕ) : ContDiff ℂ n F :=
    AnalyticOnNhd.contDiff (fun z _ => hF.analyticAt z)
  have hH' (n : ℕ) : ContDiff ℂ n H :=
    AnalyticOnNhd.contDiff (fun z _ => hH.analyticAt z)
  have hFc : ContDiff ℂ d (fun r : ℂ => F (c*r)) :=
    (hF' d).comp (contDiff_const.mul contDiff_id)
  have hHc : ContDiff ℂ d (fun r : ℂ => H (c*r)) :=
    (hH' d).comp (contDiff_const.mul contDiff_id)
  rw [iteratedDeriv_fun_mul hFc.contDiffAt hHc.contDiffAt, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  have hid := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [iteratedDeriv_comp_const_mul (hF' i), iteratedDeriv_comp_const_mul (hH' (d-i))]
  simp only [mul_zero]
  have hpow : c^i * c^(d-i) = c^d := by rw [← pow_add, Nat.add_sub_of_le hid]
  unfold pairDescendantCoeff
  rw [← sqrt_choose_factorial d i hid]
  have hs (n : ℕ) : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (by positivity)
  field_simp [hs i, hs (d-i), hs d]
  have hc := congrArg (fun x : ℂ => x *
    ((d.choose i : ℂ) * iteratedDeriv i F 0 * iteratedDeriv (d-i) H 0)) hpow
  dsimp [c] at hc
  linear_combination hc

theorem pairSection_scaled_factor (G : Geometry) (theta : Twist)
    (a : PairIndex G theta) (z : ℂ) :
    chargeTwoScaledFactor G theta (pairSection G theta a) ((scale:ℂ)*z) =
      canonicalRawStripped G theta (orbitalBasis G theta a.1) z *
        canonicalRawStripped G theta (orbitalBasis G theta a.2) z := by
  apply mul_left_cancel₀ (gaussianFactor_ne_zero 2 z)
  rw [← chargeTwoScaledFactor_factor, pairSection_apply, pairProduct,
    canonicalRawStripped_factor G theta (orbitalBasis G theta a.1),
    canonicalRawStripped_factor G theta (orbitalBasis G theta a.2)]
  rw [show gaussianFactor 2 z = gaussianFactor 1 z * gaussianFactor 1 z from
    by convert gaussianFactor_add_charge 1 1 z using 1; norm_num]
  ring

theorem pairSection_centered_factor (G : Geometry) (theta : Twist)
    (a : PairIndex G theta) (R r : ℂ) :
    chargeTwoCenteredFactor G theta (pairSection G theta a) R r =
      translatedStrippedFactor (-R) (canonicalRawStripped G theta (orbitalBasis G theta a.1))
        (((scale:ℂ)/2)*r) *
      translatedStrippedFactor (-R) (canonicalRawStripped G theta (orbitalBasis G theta a.2))
        (((scale:ℂ)/2)*r) := by
  unfold chargeTwoCenteredFactor translatedStrippedFactor
  have harg : r - -((scale:ℂ)*R) = (scale:ℂ)*(((scale:ℂ)/2)*r - -R) := by
    linear_combination -(r/2) * scale_complex_sq
  rw [harg, pairSection_scaled_factor]
  rw [show (Complex.exp (((scale:ℂ)/2*r)*conj (-R)-(-R*conj (-R))/2) *
        canonicalRawStripped G theta (orbitalBasis G theta a.1) ((scale:ℂ)/2*r - -R)) *
      (Complex.exp (((scale:ℂ)/2*r)*conj (-R)-(-R*conj (-R))/2) *
        canonicalRawStripped G theta (orbitalBasis G theta a.2) ((scale:ℂ)/2*r - -R)) =
      (Complex.exp (((scale:ℂ)/2*r)*conj (-R)-(-R*conj (-R))/2) *
        Complex.exp (((scale:ℂ)/2*r)*conj (-R)-(-R*conj (-R))/2)) *
      (canonicalRawStripped G theta (orbitalBasis G theta a.1) ((scale:ℂ)/2*r - -R) *
        canonicalRawStripped G theta (orbitalBasis G theta a.2) ((scale:ℂ)/2*r - -R)) by ring]
  congr 1
  rw [← Complex.exp_add]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_ofReal]
  linear_combination -(R * conj R / 2) * scale_complex_sq

/-- Exact original raw single-particle jet formula for the charge-two
pair descendant; its normalization is inherited from the physical contact. -/
theorem chargeTwoJetEvaluation_pairSection (G : Geometry) (theta : Twist)
    (d : ℕ) (R : ℂ) (a : PairIndex G theta) :
    chargeTwoJetEvaluation G theta d R (pairSection G theta a) =
      ∑ i ∈ Finset.range (d+1), pairDescendantCoeff d i *
        canonicalJetEvaluation G theta i R (orbitalBasis G theta a.1) *
        canonicalJetEvaluation G theta (d-i) R (orbitalBasis G theta a.2) := by
  rw [chargeTwoJetEvaluation_eq_derivative]
  rw [show chargeTwoCenteredFactor G theta (pairSection G theta a) R =
    (fun r => translatedStrippedFactor (-R)
      (canonicalRawStripped G theta (orbitalBasis G theta a.1)) (((scale:ℂ)/2)*r) *
      translatedStrippedFactor (-R)
      (canonicalRawStripped G theta (orbitalBasis G theta a.2)) (((scale:ℂ)/2)*r)) from
      funext (pairSection_centered_factor G theta a R)]
  exact normalized_com_leibniz d _ _
    (translatedStrippedFactor_differentiable _ _ (canonicalRawStripped_differentiable _ _ _))
    (translatedStrippedFactor_differentiable _ _ (canonicalRawStripped_differentiable _ _ _))

/-- Annihilation in the original canonical raw jet, in the actual orbital
basis. The coefficient is conjugate-first Riesz evaluation, not a new mode. -/
def singleJetAnnihilator (G : Geometry) (theta : Twist) (j : ℕ) (R : ℂ) :
    Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ →ₗ[ℂ]
      Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ :=
  modeAnnihilate ((orbitalBasis G theta).repr (rawPlaneJet G theta j R))

theorem singleJetAnnihilator_apply (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    singleJetAnnihilator G theta j R p =
      ∑ i, canonicalJetEvaluation G theta j R (orbitalBasis G theta i) • annihilate i p := by
  simp only [singleJetAnnihilator, modeAnnihilate, LinearMap.sum_apply, LinearMap.smul_apply,
    OrthonormalBasis.repr_apply_apply, Complex.star_def, inner_conj_symm]
  simp_rw [rawPlaneJet_inner_reproduces, canonicalJetEvaluation_apply]

/-- The charge-two COM descendant pair, whose original single-jet formula
is proved below rather than assumed. -/
def pairDescendant (G : Geometry) (theta : Twist) (d : ℕ) (R : ℂ) :
    Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ →ₗ[ℂ]
      Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ :=
  ∑ a : PairIndex G theta,
    chargeTwoJetEvaluation G theta d R (pairSection G theta a) • TwoBodyLift.pairRemove a

/-- The paper's original B_d = (sqrt 2)^{-1} sum_i positive-binomial
 a_{d-i} a_i. The annihilation order is immaterial on the bosonic core. -/
theorem pairDescendant_eq_raw (G : Geometry) (theta : Twist) (d : ℕ) (R : ℂ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    pairDescendant G theta d R p = ((Real.sqrt 2)⁻¹ : ℂ) •
      ∑ i ∈ Finset.range (d+1), pairDescendantCoeff d i •
        singleJetAnnihilator G theta (d-i) R (singleJetAnnihilator G theta i R p) := by
  classical
  simp only [pairDescendant, LinearMap.sum_apply, LinearMap.smul_apply]
  simp_rw [chargeTwoJetEvaluation_pairSection]
  simp only [Finset.sum_smul]
  rw [Finset.sum_comm]
  simp only [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [singleJetAnnihilator_apply G theta i R p]
  simp only [map_sum, map_smul]
  simp_rw [singleJetAnnihilator_apply]
  simp only [Fintype.sum_prod_type, TwoBodyLift.pairRemove, LinearMap.smul_apply,
    LinearMap.comp_apply, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  ring

@[simp] theorem pairDescendant_zero (G : Geometry) (theta : Twist) (R : ℂ) :
    pairDescendant G theta 0 R = modePair (evaluationCoordinates G theta R) := by
  apply LinearMap.ext
  intro p
  rw [modePair_evaluation_expansion]
  simp only [pairDescendant, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  rw [chargeTwoJetEvaluation_pairSection]
  simp [pairDescendantCoeff, canonicalJetEvaluation_zero, lllEvaluation_apply, pairProduct]

theorem pairDescendant_commute (G : Geometry) (theta : Twist) (d e : ℕ) (R S : ℂ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) :
    pairDescendant G theta d R (pairDescendant G theta e S p) =
      pairDescendant G theta e S (pairDescendant G theta d R p) := by
  simp only [pairDescendant, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [BosonLiftSquare.pairRemove_commute, mul_comm]

theorem pairDescendant_pair_core (G : Geometry) (theta : Twist) (N d e : ℕ) (R S : ℂ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (z : Configuration N) :
    coreFunction G theta N (pairDescendant G theta e S (pairDescendant G theta d R p)) z =
      ∑ a : PairIndex G theta, ∑ b : PairIndex G theta,
        chargeTwoJetEvaluation G theta d R (pairSection G theta a) *
        chargeTwoJetEvaluation G theta e S (pairSection G theta b) *
        coreFunction G theta N (TwoBodyLift.pairRemove b (TwoBodyLift.pairRemove a p)) z := by
  simp only [pairDescendant, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    Finset.smul_sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The original finite C_d combination of canonical B_p descendants. -/
def fourBodyJet (G : Geometry) (theta : Twist) (d : ℕ) (R : ℂ) :
    Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ →ₗ[ℂ]
      Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ :=
  ∑ i ∈ Finset.range (d+1), relativeBinomialCoeff d i •
    (pairDescendant G theta i R).comp (pairDescendant G theta (d-i) R)

/-- All spectator values of the true relative-jet tensor map equal the
original finite C_d annihilator combination. -/
theorem relativeJet_doublePairTensor (G : Geometry) (theta : Twist) (N d : ℕ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ) (z : Configuration N) (R : ℂ) :
    (relativeJet G theta 2 2 d (doublePairTensor G theta N p z)).val R =
      coreFunction G theta N (fourBodyJet G theta d R p) z := by
  change lllEvaluation G theta 4 R
    (relativeJet G theta 2 2 d (doublePairTensor G theta N p z)) = _
  simp only [doublePairTensor, map_sum, map_smul, smul_eq_mul]
  simp only [lllEvaluation_apply]
  simp_rw [relativeJet_tmul_leibniz]
  simp only [Finset.mul_sum]
  unfold fourBodyJet
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum,
    map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hcomm (i : ℕ) : pairDescendant G theta i R (pairDescendant G theta (d-i) R p) =
      pairDescendant G theta (d-i) R (pairDescendant G theta i R p) :=
    pairDescendant_commute G theta i (d-i) R R p
  simp_rw [hcomm, pairDescendant_pair_core G theta N]
  simp only [Finset.mul_sum]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem relativeJet_physicalDoublePairTensor (G : Geometry) (theta : Twist) (N d : ℕ)
    (f : PhysicalBosonCarrier G theta ((N+2)+2)) (z : Configuration N) (R : ℂ) :
    (relativeJet G theta 2 2 d (physicalDoublePairTensor G theta N f z)).val R =
      coreFunction G theta N (fourBodyJet G theta d R
        ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val) z :=
  relativeJet_doublePairTensor G theta N d _ z R

theorem pairDescendant_sector (G : Geometry) (theta : Twist) (N d : ℕ) (R : ℂ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (hp : p.IsHomogeneous (N+2)) :
    (pairDescendant G theta d R p).IsHomogeneous N := by
  simp only [pairDescendant, LinearMap.sum_apply, LinearMap.smul_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro a _
  rw [MvPolynomial.smul_eq_C_mul]
  exact (TwoBodyLift.pairRemove_sector a N p hp).C_mul _

theorem fourBodyJet_sector (G : Geometry) (theta : Twist) (N d : ℕ) (R : ℂ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (hp : p.IsHomogeneous ((N+2)+2)) :
    (fourBodyJet G theta d R p).IsHomogeneous N := by
  simp only [fourBodyJet, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro i _
  rw [MvPolynomial.smul_eq_C_mul]
  exact (pairDescendant_sector G theta N i R _
    (pairDescendant_sector G theta (N+2) (d-i) R p hp)).C_mul _

/-- Physical spectator Parseval for the actual C_d output, with no extra
factorial or particle-dependent bound. -/
theorem fourBodyJet_spectator_normSq (G : Geometry) (theta : Twist) (N d : ℕ) (R : ℂ)
    (p : Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ)
    (hp : p.IsHomogeneous ((N+2)+2)) :
    (∫ z, ‖(relativeJet G theta 2 2 d (doublePairTensor G theta N p z)).val R‖^2
      ∂sectorMeasure G N) = occupationMetricNormSq (fun _ => 1) (fourBodyJet G theta d R p) := by
  simp_rw [relativeJet_doublePairTensor]
  exact coreFunction_normSq G theta N _ (fourBodyJet_sector G theta N d R p hp)

end TorusLean.Shared.BosonRelativeFrame
