import torus.shared.FermionRelativeFrameSections
import torus.shared.ParameterRawJetLadderActions
import torus.shared.ParameterLadderProduct

/-! Rebuilt successfully with Lean 4.34.1 in the selected 3,177-module closure.
See [validation scope](../../../REBUILD.md) and ../../../REBUILD_VALIDATION.json.
The actual magnetic IBP that pairs the four fermionic S3
signs. The key scalar identity is proved from a true LLL₂ section and the
existing parameter adjoint theorem. Neither the target IBP identity nor
vanishing of a boundary remainder is imposed as a hypothesis. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiMagneticIBP
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalFermionNormalSquare
open TorusLean.Shared.PhysicalFermionJetPair
open TorusLean.Shared.FermionRelativeFrame TorusLean.Shared.PlaneJetMembership
open TorusLean.Shared.ParameterCellAdjoint TorusLean.Shared.ParameterRawJetLadder
open TorusLean.Shared.ParameterLadderProduct
open scoped BigOperators ComplexConjugate ContDiff

private theorem chargeTwo_contDiff (G : Geometry) (theta : Twist)
    (f : LLL G theta 2) : ContDiff ℝ ∞ f.val := by
  obtain ⟨F,hF,hfactor⟩ := f.property.1
  have he : f.val = fun z => gaussianFactor 2 z * F z := by
    funext z
    exact hfactor z
  rw [he]
  have hg : ContDiff ℝ ∞ (gaussianFactor 2) := by
    unfold gaussianFactor
    have hc : ContDiff ℝ ∞ (fun z : ℂ => -((2:ℝ):ℂ)*(z*conj z)/2) :=
      (contDiff_const.mul (contDiff_id.mul Complex.conjCLE.contDiff)).div_const 2
    exact hc.cexp
  exact hg.mul (hF.contDiff.restrict_scalars ℝ)

private theorem chargeTwo_dual_boundary (G : Geometry) (theta : Twist)
    (f : LLL G theta 2) : HasDualBoundary G theta 2 (fun S => conj (f.val S)) := by
  simpa only [HasDualBoundary, Complex.conj_conj] using f.property.2

private theorem gaussianTwo_wirtingerBar (S : ℂ) :
    parameterWirtingerBar (gaussianFactor 2) S = -S * gaussianFactor 2 S := by
  have hg : Differentiable ℝ (gaussianFactor 1) := by unfold gaussianFactor; fun_prop
  have he : gaussianFactor 2 = fun z => gaussianFactor 1 z * gaussianFactor 1 z :=
    funext (fun z => (gaussian_one_mul_self z).symm)
  rw [he, wirtingerBar_mul _ _ hg hg, (wirtinger_gaussian S).2]
  ring

/-- The conjugate of an actual charge-two LLL section is an actual parameter
vacuum. It follows from its Gaussian-holomorphic factorization. -/
theorem chargeTwo_dual_lower_zero (G : Geometry) (theta : Twist)
    (f : LLL G theta 2) : parameterLower 2 (fun S => conj (f.val S)) = 0 := by
  obtain ⟨F,hF,hfactor⟩ := f.property.1
  have he : f.val = fun z => gaussianFactor 2 z * F z := by
    funext z
    exact hfactor z
  rw [he]
  have hg : Differentiable ℝ (gaussianFactor 2) := by unfold gaussianFactor; fun_prop
  have hFr := hF.restrictScalars ℝ
  funext S
  unfold parameterLower
  rw [(wirtinger_conj (fun z => gaussianFactor 2 z * F z) (hg.mul hFr) S).1,
    wirtingerBar_mul _ _ hg hFr, gaussianTwo_wirtingerBar,
    (wirtinger_holomorphic F hF S).2]
  simp only [mul_zero, add_zero, map_mul, map_neg, Complex.conj_conj,
    Nat.cast_ofNat, Pi.zero_apply]
  ring

private theorem scalar_integrable (G : Geometry) (theta : Twist)
    (a b : LLL G theta 1) (f : LLL G theta 2) (i j : ℕ) :
    Integrable (fun S => dualRawJetScalar G theta a i S *
      dualRawJetScalar G theta b j S * f.val S) (cellMeasure G 2) :=
  continuous_integrable_cellMeasure G 2
    (((dualRawJetScalar_contDiff G theta a i).continuous.mul
      (dualRawJetScalar_contDiff G theta b j).continuous).mul
        (chargeTwo_contDiff G theta f).continuous)

/-- True original-cell scalar IBP. Both differentiated factors are actual
charge-one dual jet coefficients and the remaining factor is the actual
charge-two section. The minus sign comes from the genuine adjoint identity. -/
theorem scalar_derivative_edge_integral (G : Geometry) (theta : Twist)
    (a b : LLL G theta 1) (f : LLL G theta 2) :
    (∫ S, dualRawJetScalar G theta a 1 S *
      dualRawJetScalar G theta b 0 S * f.val S ∂cellMeasure G 2) =
      -(∫ S, dualRawJetScalar G theta a 0 S *
        dualRawJetScalar G theta b 1 S * f.val S ∂cellMeasure G 2) := by
  let A := dualRawJetScalar G theta a 0
  let B := dualRawJetScalar G theta b 0
  let F := fun S => conj (f.val S)
  have hA : ContDiff ℝ ∞ A := dualRawJetScalar_contDiff G theta a 0
  have hB : ContDiff ℝ ∞ B := dualRawJetScalar_contDiff G theta b 0
  have hF : ContDiff ℝ ∞ F := Complex.conjCLE.contDiff.comp (chargeTwo_contDiff G theta f)
  have hbA : HasDualBoundary G theta 1 A := dualRawJetScalar_hasDualBoundary G theta a 0
  have hbB : HasDualBoundary G theta 1 B := dualRawJetScalar_hasDualBoundary G theta b 0
  have hprod : HasDualBoundary G theta 2 (fun S => A S*B S) :=
    hasDualBoundary_mul G theta 1 1 A B hbA hbB
  have hadj := parameterLower_adjoint G theta 2 F (fun S => A S*B S)
    (hF.of_le (by simp)) ((hA.mul hB).of_le (by simp))
    (chargeTwo_dual_boundary G theta f) hprod
  have hl : parameterLower 2 F=0 := chargeTwo_dual_lower_zero G theta f
  rw [hl] at hadj
  have hz : cellInner G 2 F (parameterRaise 2 (fun S => A S*B S))=0 := by
    simpa only [cellInner, Pi.zero_apply, map_zero, zero_mul, integral_zero] using hadj.symm
  have hr : (fun S => dualRawJetScalar G theta a 1 S * B S +
      A S * dualRawJetScalar G theta b 1 S) =
      (Real.sqrt (2:ℝ):ℂ) • parameterRaise 2 (fun S => A S*B S) := by
    funext S
    have hh := parameterRaise_mul 1 1 A B
      (hA.differentiable (by simp)) (hB.differentiable (by simp)) S
    have ha := congrFun (dualRawJetScalar_raise G theta a 0) S
    have hb := congrFun (dualRawJetScalar_raise G theta b 0) S
    norm_num only [Nat.reduceAdd, Nat.cast_one, Real.sqrt_one, Complex.ofReal_one,
      one_mul, Pi.smul_apply, smul_eq_mul] at hh ha hb ⊢
    change parameterRaise 1 A S = _ at ha
    change parameterRaise 1 B S = _ at hb
    rw [ha,hb] at hh
    exact hh.symm
  have hsum : (∫ S, (dualRawJetScalar G theta a 1 S * B S +
      A S * dualRawJetScalar G theta b 1 S) * f.val S ∂cellMeasure G 2)=0 := by
    calc
      _ = cellInner G 2 F (fun S => dualRawJetScalar G theta a 1 S * B S +
          A S * dualRawJetScalar G theta b 1 S) := by
        unfold cellInner
        apply integral_congr_ae
        filter_upwards [] with S
        simp only [F, Complex.conj_conj]
        ring
      _ = 0 := by rw [hr,cellInner_smul_right,hz,mul_zero]
  simp only [add_mul,A,B] at hsum
  rw [integral_add (scalar_integrable G theta a b f 1 0)
    (scalar_integrable G theta a b f 0 1)] at hsum
  exact eq_neg_of_add_eq_zero_left hsum

/-- The scalar identity consumed by the original finite section expansion:
no derivative is applied to an isolated non-holomorphic ordered raw pair. -/
theorem pairSection_derivative_edge_integral (G : Geometry) (theta : Twist)
    (i : ℕ) (R : ℂ) (b : LLL G theta 1)
    (p : TorusLean.Shared.FermionRelativeFrame.PairIndex G theta) :
    (∫ S, rawGram (physicalQ G theta) (physicalJetCoordinates G theta i R)
      (physicalJetCoordinates G theta 1 S) *
      dualRawJetScalar G theta b 0 S * (pairSection G theta p).val S
        ∂cellMeasure G 2) =
      -(∫ S, rawGram (physicalQ G theta) (physicalJetCoordinates G theta i R)
        (physicalJetCoordinates G theta 0 S) *
        dualRawJetScalar G theta b 1 S * (pairSection G theta p).val S
          ∂cellMeasure G 2) := by
  have hgram (j : ℕ) (S : ℂ) :
      rawGram (physicalQ G theta) (physicalJetCoordinates G theta i R)
        (physicalJetCoordinates G theta j S) =
        dualRawJetScalar G theta (rawPlaneJet G theta i R) j S := by
    rw [physicalJetCoordinates, physicalJetCoordinates, physicalOrbitalCoordinates_gram]
    exact (lll_inner_eq_cellInner G theta 1 _ _).symm
  simp_rw [hgram]
  exact scalar_derivative_edge_integral G theta (rawPlaneJet G theta i R) b
    (pairSection G theta p)

end TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiMagneticIBP
