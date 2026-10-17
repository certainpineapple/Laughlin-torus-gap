import torus.shared.FermionLocalJetFourCouplingOriginalVacua
import torus.shared.ThermalCoherentFermionCOMCell

/-! The original full-T columns are the actual charge-four normalized COM
family of the original highest coupled source.  The finite integer checks
supply the raising recurrence; no recurrence, vacuum, injectivity or raw-map
isometry is added as a hypothesis.  All statements retain the full copy label. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.ThermalCoherentFermionJetWord
open TorusLean.Shared.ThermalCoherentFermionCOMWords
open TorusLean.Shared.ParameterLadderIntegration
open TorusLean.Shared.ParameterRawJetLadder
open TorusLean.Shared.ParameterCellAdjoint
open scoped ContDiff BigOperators

/-- This is the dual of the original source, not a newly defined ladder. -/
theorem original_descendant_dual_raise (G : Geometry) (theta : Twist)
    (q : Space (physicalQ G theta)) (d : Fin 23) (r : OddMode (d.val+1))
    (n : ℕ) (hn : d.val+1+n<23) (R : ℂ) :
    parameterRaise 4
      (wordDual G theta 4 q (descendantWords (d.val+1) (d.val+1+n) r.val.val)) R =
    (Real.sqrt (n+1:ℝ):ℂ) *
      wordDual G theta 4 q (descendantWords (d.val+1) (d.val+1+(n+1)) r.val.val) R := by
  let T : Fin 24 := ⟨d.val+1+n,by omega⟩
  have hr := original_descendant_raise d T r (by dsimp [T]; omega) (by simpa [T] using hn)
  have hv := congrArg
    (fun v : FormalExterior => exteriorSeedDualLinearMap G theta q v R) hr
  simp only [map_smul,Pi.smul_apply,smul_eq_mul] at hv
  rw [← realize_descendantWords] at hv
  change wordDual G theta 4 q
      (wordRaise 4 (descendantWords (d.val+1) T.val r.val.val)) R = _ at hv
  have hT : (T.val : ℝ)-((d.val : ℝ)+1)+1=(n : ℝ)+1 := by
    dsimp [T]
    push_cast
    ring
  have hnext : T.val+1=d.val+1+(n+1) := by dsimp [T]; omega
  rw [hT,hnext] at hv
  change wordDual G theta 4 q
      (wordRaise 4 (descendantWords (d.val+1) (d.val+1+n) r.val.val)) R =
      (2*(Real.sqrt (n+1:ℝ):ℂ)) * wordDual G theta 4 q
        (descendantWords (d.val+1) (d.val+1+(n+1)) r.val.val) R at hv
  have ha := wordDual_raise G theta 4 q
    (descendantWords (d.val+1) (d.val+1+n) r.val.val) R
  have hsqrt4 : Real.sqrt (4:ℝ)=2 := by
    simpa only [show (2:ℝ)^2=4 by norm_num] using
      Real.sqrt_sq (show (0:ℝ)≤2 by norm_num)
  have hsqrt4c : (Real.sqrt (4:ℝ):ℂ)=(2:ℂ) := by exact_mod_cast hsqrt4
  simp only [Nat.cast_ofNat] at ha
  rw [hsqrt4c] at ha
  have h := ha.trans hv
  linear_combination (1/2:ℂ)*h

/-- The unnormalized true parameter ladder differs from the original full-T
source by precisely sqrt(n!), with no extra charge or ordered-pair factor. -/
theorem original_comDual_factorial (G : Geometry) (theta : Twist)
    (q : Space (physicalQ G theta)) (d : Fin 23) (r : OddMode (d.val+1))
    (n : ℕ) (hn : d.val+1+n≤23) :
    comDual G theta 4 q (highestCoupledWords (d.val+1) r) n =
      factorialRootNat n •
        wordDual G theta 4 q (descendantWords (d.val+1) (d.val+1+n) r.val.val) := by
  induction n with
  | zero =>
    simp only [comDual,comSource,highestCoupledWords,Nat.add_zero,
      factorialRootNat,Nat.factorial_zero,Nat.cast_one,Real.sqrt_one,
      Complex.ofReal_one,one_smul]
  | succ n ih =>
    rw [← comDual_raise,ih (by omega)]
    funext R
    change parameterRaise 4
      (fun z => factorialRootNat n * wordDual G theta 4 q
        (descendantWords (d.val+1) (d.val+1+n) r.val.val) z) R = _
    rw [parameterRaise_const_mul _ _ _
      ((wordDual_contDiff G theta 4 q _).differentiable (by simp)),
      original_descendant_dual_raise G theta q d r n (by omega),factorialRootNat_succ]
    simp only [Pi.smul_apply,smul_eq_mul]
    ring

theorem original_normalized_comDual (G : Geometry) (theta : Twist)
    (q : Space (physicalQ G theta)) (d : Fin 23) (r : OddMode (d.val+1))
    (n : ℕ) (hn : d.val+1+n≤23) :
    normalizedLevel (comDual G theta 4 q (highestCoupledWords (d.val+1) r)) n =
      wordDual G theta 4 q (descendantWords (d.val+1) (d.val+1+n) r.val.val) := by
  unfold normalizedLevel
  rw [original_comDual_factorial G theta q d r n hn]
  change (factorialRootNat n)⁻¹ • (factorialRootNat n • _) = _
  rw [smul_smul,inv_mul_cancel₀ (factorialRootNat_ne_zero n),one_smul]

/-- Equality in the physical exterior space follows from all occupation-dual
matrix elements.  It neither cancels nor assumes injectivity of the raw map. -/
theorem original_normalized_com_source (G : Geometry) (theta : Twist)
    (d : Fin 23) (r : OddMode (d.val+1)) (n : ℕ)
    (hn : d.val+1+n≤23) (R : ℂ) :
    actualNormalizedCOMSource G theta 4 (highestCoupledWords (d.val+1) r) n R =
      physicalDescendantColumn G theta (d.val+1) (d.val+1+n) r.val.val R := by
  let u := actualNormalizedCOMSource G theta 4 (highestCoupledWords (d.val+1) r) n R
  let v := physicalDescendantColumn G theta (d.val+1) (d.val+1+n) r.val.val R
  have he (q : Space (physicalQ G theta)) :
      occupationInner (physicalQ G theta) q u = occupationInner (physicalQ G theta) q v := by
    change occupationInner (physicalQ G theta) q
      (actualNormalizedCOMSource G theta 4 (highestCoupledWords (d.val+1) r) n R) = _
    rw [actualNormalizedCOMSource_dual,original_normalized_comDual G theta q d r n hn]
    change exteriorSeedDual G theta q
      (realize 4 (descendantWords (d.val+1) (d.val+1+n) r.val.val)) R = _
    rw [realize_descendantWords]
    rfl
  have hz : occupationInner (physicalQ G theta) (u-v) (u-v)=0 := by
    have h := he (u-v)
    simp only [occupationInner,map_sub,Finsupp.sub_apply,mul_sub,Finset.sum_sub_distrib] at h ⊢
    exact sub_eq_zero.mpr h
  have hnorm : occupationNormSq (physicalQ G theta) (u-v)=0 := by
    have h := congrArg Complex.re hz
    simpa only [occupationInner_self,Complex.ofReal_re,Complex.zero_re] using h
  exact sub_eq_zero.mp ((occupationNormSq_eq_zero _ _).mp hnorm)

end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.original_descendant_dual_raise
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.original_comDual_factorial
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.original_normalized_comDual
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.original_normalized_com_source
