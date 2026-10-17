import torus.shared.ThermalCoherentFermionAnchoredJacobiSingleDensity
import torus.shared.MagneticBoundaryUnfolding
import torus.shared.ParameterLadderIntegration

/-! One-edge unfolding of the original fermion S3. The exterior coefficient
retains its actual torus sections. Its charge-one boundary comes from the
true dual spectator and the existing charge-two pairSection, not from a
holomorphic assumption on the individual ordered raw-jet pair. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiOneEdge
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalFermionNormalSquare
open TorusLean.Shared.ParameterCellAdjoint TorusLean.Shared.ParameterRawJetLadder
open TorusLean.Shared.MagneticBoundaryUnfolding TorusLean.Shared.ParameterLadderIntegration
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiSingleDensity
open TorusLean.Fermion.CanonicalPlaneJets TorusLean.Fermion.PlaneMagneticUnitary
open scoped BigOperators ComplexConjugate

/-- Charge two times a genuine dual charge-one scalar has the original
charge-one magnetic boundary, including the same twist. -/
theorem dual_chargeTwo_product_boundary (G : Geometry) (theta : Twist)
    (h : ℂ → ℂ) (hh : HasDualBoundary G theta 1 h) (f : LLL G theta 2) :
    HasLatticeBoundary G.M 1 G.omega1 G.omega2 theta.theta1 theta.theta2
      (fun S => h S*f.val S) := by
  apply (latticeBoundary_iff_forward _ _ _ _ _ _ _).mpr
  intro p S
  let b : ℂ := (latticeChi G.M theta.theta1 theta.theta2 p)⁻¹ *
    Complex.exp (magneticExponent (1:ℝ) S (latticePeriod G.omega1 G.omega2 p))
  have hb : ‖b‖=1 := by
    simp only [b,norm_mul,norm_inv,latticeChi_norm,magneticMultiplier_norm,
      inv_one,one_mul]
  have hc : conj b*b=1 := by
    rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,hb]
    norm_num
  have he : magneticExponent (2:ℝ) S (latticePeriod G.omega1 G.omega2 p) =
      magneticExponent (1:ℝ) S (latticePeriod G.omega1 G.omega2 p) +
        magneticExponent (1:ℝ) S (latticePeriod G.omega1 G.omega2 p) := by
    unfold magneticExponent
    push_cast
    ring
  have h2 : (latticeChi G.M theta.theta1 theta.theta2 p ^ 2)⁻¹ *
      Complex.exp (magneticExponent (2:ℝ) S (latticePeriod G.omega1 G.omega2 p)) =
      b*b := by
    rw [he,Complex.exp_add]
    simp only [b,inv_pow,pow_two]
    ring
  have hforward := (latticeBoundary_iff_forward _ _ _ _ _ _ _).mp hh p S
  simp only [Nat.cast_one,pow_one] at hforward
  change conj (h (S+latticePeriod G.omega1 G.omega2 p)) = b*conj (h S) at hforward
  have hd := congrArg (starRingEnd ℂ) hforward
  simp only [map_mul,Complex.conj_conj] at hd
  have hf := (latticeBoundary_iff_forward _ _ _ _ _ _ _).mp f.property.2 p S
  simp only [Nat.cast_ofNat,h2] at hf
  simp only [Nat.cast_one,pow_one]
  change h (S+latticePeriod G.omega1 G.omega2 p)*
    f.val (S+latticePeriod G.omega1 G.omega2 p) = b*(h S*f.val S)
  rw [hd,hf]
  calc
    _ = (conj b*b)*(b*(h S*f.val S)) := by ring
    _ = _ := by rw [hc,one_mul]

private theorem finite_sections_boundary {I J : Type*} [Fintype I] [Fintype J]
    (G : Geometry) (theta : Twist) (b : I → LLL G theta 1)
    (f : J → LLL G theta 2) (c : I → J → ℂ) (j : ℕ) :
    HasLatticeBoundary G.M 1 G.omega1 G.omega2 theta.theta1 theta.theta2
      (fun S => ∑ i, ∑ p, dualRawJetScalar G theta (b i) j S * (f p).val S * c i p) := by
  classical
  apply (latticeBoundary_iff_forward _ _ _ _ _ _ _).mpr
  intro q S
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro p _
  have hb := (latticeBoundary_iff_forward _ _ _ _ _ _ _).mp
    (dual_chargeTwo_product_boundary G theta (dualRawJetScalar G theta (b i) j)
      (dualRawJetScalar_hasDualBoundary G theta (b i) j) (f p)) q S
  change dualRawJetScalar G theta (b i) j (S+latticePeriod G.omega1 G.omega2 q) *
      (f p).val (S+latticePeriod G.omega1 G.omega2 q) = _ at hb
  rw [hb]
  ring

/-- The actual whole-Fock exterior coefficient has charge one for every
spectator index, even though it need not be holomorphic. -/
theorem exteriorCoefficient_boundary (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (j k : ℕ) (R : ℂ) :
    HasLatticeBoundary G.M 1 G.omega1 G.omega2 theta.theta1 theta.theta2
      (fun S => exteriorCoefficient G theta x y j k R S) := by
  simp_rw [exteriorCoefficient_section_expansion,← dualRawJetScalar_eq_conj]
  exact finite_sections_boundary G theta _ _ _ j

/-- The conjugate-first orientation of the original physical Gram is kept
explicit when using the existing magnetic-periodization theorem. -/
theorem exteriorCoefficient_jet_unfold (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (i j k : ℕ) (R : ℂ) :
    (∫ S, jetGram G theta i 0 R S * exteriorCoefficient G theta x y j k R S
        ∂cellMeasure G 1) =
      ∫ S, conj (translatedPlaneJet i R S) * exteriorCoefficient G theta x y j k R S
        ∂planeMeasure := by
  have he := cellInner_magneticPeriodization_eq_planeInner G theta
    (fun S => exteriorCoefficient G theta x y j k R S)
    (exteriorCoefficient_continuous G theta x y j k R)
    (exteriorCoefficient_boundary G theta x y j k R) (translatedPlaneJet i R)
    (TorusLean.Shared.MagneticCellUnfolding.translatedPlaneJet_integrable i R)
  have hc := congrArg (starRingEnd ℂ) he
  simp only [cellInner,planeInner,← integral_conj,map_mul,Complex.conj_conj] at hc
  simpa only [jetGram_zero_eq_conj_kernel,rawJetFunction,mul_comm] using hc

/-- The unfolded cross product has a genuine plane L1 domain. -/
theorem exteriorCoefficient_plane_integrable (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (i j k : ℕ) (R : ℂ) :
    Integrable (fun S => conj (translatedPlaneJet i R S) *
      exteriorCoefficient G theta x y j k R S) planeMeasure := by
  have hi := boundarySection_seed_cross_integrable G theta 1
    (fun S => exteriorCoefficient G theta x y j k R S)
    (exteriorCoefficient_continuous G theta x y j k R)
    (exteriorCoefficient_boundary G theta x y j k R) (translatedPlaneJet i R)
    (TorusLean.Shared.MagneticCellUnfolding.translatedPlaneJet_integrable i R)
  have hc := Complex.conjCLE.toContinuousLinearMap.integrable_comp hi
  change Integrable (fun S => conj (conj (exteriorCoefficient G theta x y j k R S) *
    translatedPlaneJet i R S)) planeMeasure at hc
  simpa only [map_mul,Complex.conj_conj,mul_comm] using hc

private theorem exteriorCoefficient_cellOne_integrable (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) (i j k : ℕ) (R : ℂ) :
    Integrable (fun S => jetGram G theta i 0 R S *
      exteriorCoefficient G theta x y j k R S) (cellMeasure G 1) := by
  apply continuous_integrable_cellMeasure G 1
  have hg : Continuous (fun S => jetGram G theta i 0 R S) := by
    simp_rw [jetGram_eq_dualRawJetScalar]
    exact (dualRawJetScalar_contDiff G theta
      (TorusLean.Shared.PlaneJetMembership.rawPlaneJet G theta i R) 0).continuous
  exact hg.mul (exteriorCoefficient_continuous G theta x y j k R)

/-- Exact original S3 with one internal edge unfolded. The factor four is
2 from the actual CAR/IBP plus 2 from μ₂=2μ₁. The outer original μ₂ and every
exterior torus section remain unchanged. -/
theorem matrixSingleContraction_one_edge_integral (G : Geometry) (theta : Twist)
    (x y : Space (physicalQ G theta)) :
    occupationInner (physicalQ G theta) x
      (matrixSingleContraction (physicalQ G theta) (contactMatrix G theta) y) =
      (4:ℂ) * ∫ R, ∫ S,
        -(conj (translatedPlaneJet 0 R S) * exteriorCoefficient G theta x y 1 1 R S) +
        conj (translatedPlaneJet 1 R S) * exteriorCoefficient G theta x y 1 0 R S
          ∂planeMeasure ∂cellMeasure G 2 := by
  rw [matrixSingleContraction_two_term_integral]
  have hr (R : ℂ) : (∫ S,
      -(jetGram G theta 0 0 R S * exteriorCoefficient G theta x y 1 1 R S) +
      jetGram G theta 1 0 R S * exteriorCoefficient G theta x y 1 0 R S
        ∂cellMeasure G 2) =
      (2:ℂ) * ∫ S,
        -(conj (translatedPlaneJet 0 R S) * exteriorCoefficient G theta x y 1 1 R S) +
        conj (translatedPlaneJet 1 R S) * exteriorCoefficient G theta x y 1 0 R S
          ∂planeMeasure := by
    have hm := cellIntegral_two_eq_charge G 1 (fun S =>
      -(jetGram G theta 0 0 R S * exteriorCoefficient G theta x y 1 1 R S) +
      jetGram G theta 1 0 R S * exteriorCoefficient G theta x y 1 0 R S)
    norm_num at hm
    rw [hm]
    congr 1
    have hc0 := exteriorCoefficient_cellOne_integrable G theta x y 0 1 1 R
    have hc1 := exteriorCoefficient_cellOne_integrable G theta x y 1 1 0 R
    have hp0 := exteriorCoefficient_plane_integrable G theta x y 0 1 1 R
    have hp1 := exteriorCoefficient_plane_integrable G theta x y 1 1 0 R
    have hcn : Integrable (fun S =>
      -(jetGram G theta 0 0 R S * exteriorCoefficient G theta x y 1 1 R S))
        (cellMeasure G 1) := hc0.neg
    have hpn : Integrable (fun S =>
      -(conj (translatedPlaneJet 0 R S) * exteriorCoefficient G theta x y 1 1 R S))
        planeMeasure := hp0.neg
    rw [integral_add hcn hc1,integral_neg,exteriorCoefficient_jet_unfold,
      exteriorCoefficient_jet_unfold,integral_add hpn hp1,integral_neg]
  simp_rw [hr]
  rw [integral_const_mul]
  ring

end TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiOneEdge
