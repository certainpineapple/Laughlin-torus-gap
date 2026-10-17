import torus.shared.FermionRelativeFrameJets
import torus.shared.BosonRelativeFrameJets

/-!
Exact original m=1 COM-descendant coefficients.  Only the generic normalized
Leibniz lemma is shared with the bosonic calculation.  The Wronskian,
magnetic connection cancellation, factor one half, and CAR signs below
are derived from the true fermionic pair section.

The natural index p is the COM derivative order.  Its single-particle
orbital degree is p+1; the subsequent relative C_d index remains d.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionRelativeFrame
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.PhysicalFermionM1Contact TorusLean.Shared.PhysicalFermionJetPair
open TorusLean.Shared.PhysicalFermionNormalSquare TorusLean.Shared.PhysicalFermionPairLift
open TorusLean.Shared.RelativeJetMap TorusLean.Shared.ChargeTwoScaling
open TorusLean.Shared.PlaneJetReproducing TorusLean.Shared.GroundJetReproducing
open TorusLean.Shared.PlaneJetMembership
open scoped TensorProduct ComplexConjugate BigOperators

/-- Pure normalized positive COM Leibniz weight. -/
def comCoefficient (p k : ℕ) : ℂ :=
  (Real.sqrt (p.choose k : ℝ) : ℂ) * ((scale : ℂ)/2)^p

/-- Canonical translated original orbital factor. -/
def centeredOrbital (G : Geometry) (theta : Twist)
    (i : Fin (physicalQ G theta+1)) (R : ℂ) : ℂ → ℂ :=
  translatedStrippedFactor (-R)
    (orbitalFactor G theta (physicalIndexEquiv G theta i))

lemma centeredOrbital_differentiable (G : Geometry) (theta : Twist)
    (i : Fin (physicalQ G theta+1)) (R : ℂ) :
    Differentiable ℂ (centeredOrbital G theta i R) :=
  translatedStrippedFactor_differentiable _ _ (orbitalFactor_differentiable G theta _)

/-- The connection contribution is retained until antisymmetrization. -/
lemma translatedStrippedFactor_deriv (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (R z : ℂ) :
    deriv (translatedStrippedFactor (-R) F) z =
      Complex.exp (z * conj (-R) - ((-R)*conj (-R))/2) *
        (deriv F (z-(-R)) + conj (-R) * F (z-(-R))) := by
  have harg : HasDerivAt (fun w : ℂ => w-(-R)) 1 z :=
    (hasDerivAt_id z).sub_const (-R)
  have hder := (hF (z-(-R))).hasDerivAt.comp z harg
  have hexp := (((hasDerivAt_id z).mul_const (conj (-R))).sub_const
    (((-R)*conj (-R))/2)).cexp
  have hd := (hexp.fun_mul hder).deriv
  change deriv (translatedStrippedFactor (-R) F) z = _ at hd
  rw [hd]
  simp only [id_eq, Function.comp_apply]
  ring

/-- Both magnetic connection terms cancel in the true m=1 Wronskian. -/
lemma translated_wronskian (F H : ℂ → ℂ)
    (hF : Differentiable ℂ F) (hH : Differentiable ℂ H) (R z : ℂ) :
    deriv (translatedStrippedFactor (-R) F) z * translatedStrippedFactor (-R) H z -
      translatedStrippedFactor (-R) F z * deriv (translatedStrippedFactor (-R) H) z =
    (Complex.exp (z*conj (-R)-((-R)*conj (-R))/2) *
      Complex.exp (z*conj (-R)-((-R)*conj (-R))/2)) *
      (deriv F (z-(-R))*H (z-(-R)) - F (z-(-R))*deriv H (z-(-R))) := by
  rw [translatedStrippedFactor_deriv F hF, translatedStrippedFactor_deriv H hH]
  unfold translatedStrippedFactor
  ring

/-- Scaling exposes exactly half the original Wronskian. -/
theorem pairSection_scaled_factor (G : Geometry) (theta : Twist)
    (a : PairIndex G theta) (z : ℂ) :
    chargeTwoScaledFactor G theta (pairSection G theta a) ((scale:ℂ)*z) =
      (deriv (orbitalFactor G theta (physicalIndexEquiv G theta a.1)) z *
        orbitalFactor G theta (physicalIndexEquiv G theta a.2) z -
       orbitalFactor G theta (physicalIndexEquiv G theta a.1) z *
        deriv (orbitalFactor G theta (physicalIndexEquiv G theta a.2)) z) / 2 := by
  apply mul_left_cancel₀ (gaussianFactor_ne_zero 2 z)
  rw [← chargeTwoScaledFactor_factor, pairSection_apply, rawM1PairCoefficient_derivative]
  ring

/-- Genuine centered charge-two factor, expressed in original centered
single-particle factors.  There is no additional raw-jet normalization. -/
theorem pairSection_centered_factor (G : Geometry) (theta : Twist)
    (a : PairIndex G theta) (R r : ℂ) :
    chargeTwoCenteredFactor G theta (pairSection G theta a) R r =
      (deriv (centeredOrbital G theta a.1 R) (((scale:ℂ)/2)*r) *
        centeredOrbital G theta a.2 R (((scale:ℂ)/2)*r) -
       centeredOrbital G theta a.1 R (((scale:ℂ)/2)*r) *
        deriv (centeredOrbital G theta a.2 R) (((scale:ℂ)/2)*r)) / 2 := by
  simp only [centeredOrbital]
  rw [translated_wronskian _ _
    (orbitalFactor_differentiable G theta _) (orbitalFactor_differentiable G theta _)]
  unfold chargeTwoCenteredFactor translatedStrippedFactor
  have harg : r - -((scale:ℂ)*R) = (scale:ℂ)*(((scale:ℂ)/2)*r - -R) := by
    linear_combination -(r/2) * scale_complex_sq
  rw [harg, pairSection_scaled_factor]
  have he : Complex.exp (r*conj (-((scale:ℂ)*R)) -
        (-((scale:ℂ)*R))*conj (-((scale:ℂ)*R))/2) =
      Complex.exp ((((scale:ℂ)/2)*r)*conj (-R)-((-R)*conj (-R))/2) *
        Complex.exp ((((scale:ℂ)/2)*r)*conj (-R)-((-R)*conj (-R))/2) := by
    rw [← Complex.exp_add]
    congr 1
    simp only [map_neg, map_mul, Complex.conj_ofReal]
    linear_combination -(R * conj R / 2) * scale_complex_sq
  rw [he]
  ring

lemma sqrt_factorial_succ (j : ℕ) :
    (Real.sqrt ((j+1).factorial : ℝ) : ℂ) =
      (Real.sqrt ((j+1:ℕ) : ℝ) : ℂ) * (Real.sqrt (j.factorial : ℝ) : ℂ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Real.sqrt_mul (by positivity), Complex.ofReal_mul]

/-- Raising an original normalized single jet contributes exactly sqrt(j+1). -/
lemma normalized_deriv_succ (F : ℂ → ℂ) (j : ℕ) :
    iteratedDeriv j (deriv F) 0 / (Real.sqrt (j.factorial : ℝ) : ℂ) =
      (Real.sqrt ((j+1:ℕ) : ℝ) : ℂ) *
        (iteratedDeriv (j+1) F 0 / (Real.sqrt ((j+1).factorial : ℝ) : ℂ)) := by
  rw [← iteratedDeriv_succ', sqrt_factorial_succ]
  have ha : (Real.sqrt ((j+1:ℕ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hb : (Real.sqrt (j.factorial : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
  field_simp

/-- Independent Wronskian Leibniz formula.  The two shifted branches are
kept explicit, so the antisymmetry and original minus sign are visible. -/
theorem normalized_com_wronskian (p : ℕ) (F H : ℂ → ℂ)
    (hF : Differentiable ℂ F) (hH : Differentiable ℂ H) :
    iteratedDeriv p (fun r =>
      (deriv F (((scale:ℂ)/2)*r) * H (((scale:ℂ)/2)*r) -
       F (((scale:ℂ)/2)*r) * deriv H (((scale:ℂ)/2)*r)) / 2) 0 /
      (Real.sqrt (p.factorial : ℝ) : ℂ) =
    ∑ k ∈ Finset.range (p+1), comCoefficient p k / 2 *
      ((Real.sqrt ((k+1:ℕ) : ℝ) : ℂ) *
          (iteratedDeriv (k+1) F 0 / (Real.sqrt ((k+1).factorial : ℝ) : ℂ)) *
          (iteratedDeriv (p-k) H 0 / (Real.sqrt ((p-k).factorial : ℝ) : ℂ)) -
       (Real.sqrt ((p-k+1:ℕ) : ℝ) : ℂ) *
          (iteratedDeriv k F 0 / (Real.sqrt (k.factorial : ℝ) : ℂ)) *
          (iteratedDeriv (p-k+1) H 0 / (Real.sqrt ((p-k+1).factorial : ℝ) : ℂ))) := by
  have hDF : Differentiable ℂ (deriv F) := hF.deriv
  have hDH : Differentiable ℂ (deriv H) := hH.deriv
  have hf : ContDiff ℂ p (fun r : ℂ => deriv F (((scale:ℂ)/2)*r) * H (((scale:ℂ)/2)*r)) :=
    (hDF.contDiff.comp (contDiff_const.mul contDiff_id)).mul
      (hH.contDiff.comp (contDiff_const.mul contDiff_id))
  have hh : ContDiff ℂ p (fun r : ℂ => F (((scale:ℂ)/2)*r) * deriv H (((scale:ℂ)/2)*r)) :=
    (hF.contDiff.comp (contDiff_const.mul contDiff_id)).mul
      (hDH.contDiff.comp (contDiff_const.mul contDiff_id))
  rw [iteratedDeriv_div_const, iteratedDeriv_fun_sub hf.contDiffAt hh.contDiffAt]
  rw [show ∀ x y s : ℂ, ((x-y)/2)/s = (x/s-y/s)/2 by intros; ring]
  rw [BosonRelativeFrame.normalized_com_leibniz p (deriv F) H hDF hH,
    BosonRelativeFrame.normalized_com_leibniz p F (deriv H) hF hDH,
    ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [normalized_deriv_succ F k, normalized_deriv_succ H (p-k)]
  unfold comCoefficient BosonRelativeFrame.pairDescendantCoeff
  ring

/-- Exact raw single-particle-jet coefficients of the actual charge-two
m=1 descendant, including all factorials and the ordered-pair half. -/
theorem chargeTwoJetEvaluation_pairSection (G : Geometry) (theta : Twist)
    (p : ℕ) (R : ℂ) (a : PairIndex G theta) :
    chargeTwoJetEvaluation G theta p R (pairSection G theta a) =
      ∑ k ∈ Finset.range (p+1), comCoefficient p k / 2 *
        ((Real.sqrt ((k+1:ℕ) : ℝ) : ℂ) *
            rawJetCoefficient G theta (orbitalBasis G theta (physicalIndexEquiv G theta a.1)) (k+1) R *
            rawJetCoefficient G theta (orbitalBasis G theta (physicalIndexEquiv G theta a.2)) (p-k) R -
         (Real.sqrt ((p-k+1:ℕ) : ℝ) : ℂ) *
            rawJetCoefficient G theta (orbitalBasis G theta (physicalIndexEquiv G theta a.1)) k R *
            rawJetCoefficient G theta (orbitalBasis G theta (physicalIndexEquiv G theta a.2)) (p-k+1) R) := by
  rw [chargeTwoJetEvaluation_eq_derivative]
  rw [show chargeTwoCenteredFactor G theta (pairSection G theta a) R =
      (fun r => (deriv (centeredOrbital G theta a.1 R) (((scale:ℂ)/2)*r) *
        centeredOrbital G theta a.2 R (((scale:ℂ)/2)*r) -
       centeredOrbital G theta a.1 R (((scale:ℂ)/2)*r) *
        deriv (centeredOrbital G theta a.2 R) (((scale:ℂ)/2)*r)) / 2) from
      funext (pairSection_centered_factor G theta a R)]
  exact normalized_com_wronskian p _ _
    (centeredOrbital_differentiable G theta a.1 R)
    (centeredOrbital_differentiable G theta a.2 R)

/-- A pair of original jets expanded in the same physical CAR modes. -/
lemma rawJetPair_expansion (G : Geometry) (theta : Twist) (i j : ℕ) (R : ℂ) :
    rawPairAnnihilate (physicalQ G theta) (physicalJetCoordinates G theta i R)
      (physicalJetCoordinates G theta j R) =
    ∑ a : PairIndex G theta,
      (rawJetCoefficient G theta (orbitalBasis G theta (physicalIndexEquiv G theta a.1)) i R *
       rawJetCoefficient G theta (orbitalBasis G theta (physicalIndexEquiv G theta a.2)) j R) •
        modePairAnnihilate (physicalQ G theta) a := by
  rw [rawPairAnnihilate_expansion]
  simp only [physicalJetCoordinates_star]

/-- Exact original CAR operator formula before the finite reindexing that
combines the two shifted branches into the paper's (i-j) coefficient. -/
theorem pairDescendant_eq_raw_two_branch (G : Geometry) (theta : Twist)
    (p : ℕ) (R : ℂ) :
    pairDescendant G theta p R =
      ∑ k ∈ Finset.range (p+1), (comCoefficient p k / 2) •
        ((Real.sqrt ((k+1:ℕ) : ℝ) : ℂ) •
          rawPairAnnihilate (physicalQ G theta)
            (physicalJetCoordinates G theta (k+1) R) (physicalJetCoordinates G theta (p-k) R) -
         (Real.sqrt ((p-k+1:ℕ) : ℝ) : ℂ) •
          rawPairAnnihilate (physicalQ G theta)
            (physicalJetCoordinates G theta k R) (physicalJetCoordinates G theta (p-k+1) R)) := by
  classical
  unfold pairDescendant
  simp_rw [chargeTwoJetEvaluation_pairSection, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  rw [rawJetPair_expansion, rawJetPair_expansion]
  simp only [Finset.smul_sum, smul_sub, smul_smul, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  module

/-- The CAR reversal is valid for arbitrary actual raw jets, without any
orthogonality or unit-norm assumption. -/
lemma rawJetPair_swap (G : Geometry) (theta : Twist) (i j : ℕ) (R : ℂ) :
    rawPairAnnihilate (physicalQ G theta) (physicalJetCoordinates G theta j R)
      (physicalJetCoordinates G theta i R) =
    -rawPairAnnihilate (physicalQ G theta) (physicalJetCoordinates G theta i R)
      (physicalJetCoordinates G theta j R) := by
  apply LinearMap.ext
  intro x
  exact vectorAnnihilate_anticomm_apply (physicalQ G theta)
    (physicalJetCoordinates G theta i R) (physicalJetCoordinates G theta j R) x

/-- Reflection of the second branch and the actual CAR minus sign remove
exactly the ordered-pair half.  This is the one-branch precursor of eq:F-pair. -/
theorem pairDescendant_eq_raw_single_branch (G : Geometry) (theta : Twist)
    (p : ℕ) (R : ℂ) :
    pairDescendant G theta p R =
      ∑ k ∈ Finset.range (p+1),
        (comCoefficient p k * (Real.sqrt ((k+1:ℕ) : ℝ) : ℂ)) •
          rawPairAnnihilate (physicalQ G theta)
            (physicalJetCoordinates G theta (k+1) R) (physicalJetCoordinates G theta (p-k) R) := by
  classical
  let A : ℕ → ℕ → Module.End ℂ (Space (physicalQ G theta)) := fun i j =>
    rawPairAnnihilate (physicalQ G theta)
      (physicalJetCoordinates G theta i R) (physicalJetCoordinates G theta j R)
  let U : ℕ → Module.End ℂ (Space (physicalQ G theta)) := fun k =>
    (comCoefficient p k * (Real.sqrt ((k+1:ℕ) : ℝ) : ℂ)) • A (k+1) (p-k)
  let V : ℕ → Module.End ℂ (Space (physicalQ G theta)) := fun k =>
    (comCoefficient p k * (Real.sqrt ((p-k+1:ℕ) : ℝ) : ℂ)) • A k (p-k+1)
  have hflip : (∑ k ∈ Finset.range (p+1), V k) =
      -(∑ k ∈ Finset.range (p+1), U k) := by
    calc
      _ = ∑ k ∈ Finset.range (p+1), V (p-k) := (Finset.sum_flip V).symm
      _ = _ := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        have hkp : k ≤ p := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
        have hc : comCoefficient p (p-k) = comCoefficient p k := by
          unfold comCoefficient
          rw [Nat.choose_symm hkp]
        dsimp only [V, U]
        rw [Nat.sub_sub_self hkp, hc]
        rw [show A (p-k) (k+1) = -A (k+1) (p-k) from
          rawJetPair_swap G theta (k+1) (p-k) R]
        rw [smul_neg]
  rw [pairDescendant_eq_raw_two_branch]
  change _ = ∑ k ∈ Finset.range (p+1), U k
  calc
    _ = (2 : ℂ)⁻¹ • ((∑ k ∈ Finset.range (p+1), U k) -
        (∑ k ∈ Finset.range (p+1), V k)) := by
      rw [← Finset.sum_sub_distrib, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      dsimp only [U, V, A]
      module
    _ = _ := by rw [hflip]; module

/-- The established zero descendant is literally the original -u0 wedge u1
CAR pair, rather than a renormalized proxy. -/
theorem pairDescendant_zero_original (G : Geometry) (theta : Twist) (R : ℂ) :
    pairDescendant G theta 0 R =
      rawPairAnnihilate (physicalQ G theta) (-physicalJetCoordinates G theta 0 R)
        (physicalJetCoordinates G theta 1 R) :=
  pairDescendant_zero G theta R

#print axioms translated_wronskian
#print axioms pairSection_centered_factor
#print axioms normalized_com_wronskian
#print axioms chargeTwoJetEvaluation_pairSection
#print axioms pairDescendant_eq_raw_two_branch
#print axioms pairDescendant_eq_raw_single_branch
#print axioms rawJetPair_swap
#print axioms pairDescendant_zero_original
end TorusLean.Shared.FermionRelativeFrame
