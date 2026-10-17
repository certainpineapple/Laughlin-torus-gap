import torus.shared.FermionRelativeFrameSections

/-! Full spectator-valued charge-two tensor for the two original m=1 CAR
annihilations.  The fixed-N space is the complete physical fermion carrier,
identified only through its previously proved exterior equivalence. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.FermionRelativeFrame
open MeasureTheory TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.PhysicalFermionCarrier TorusLean.Shared.PhysicalFermionExterior
open TorusLean.Shared.PhysicalFermionPairContraction TorusLean.Shared.PhysicalFermionPairLift
open TorusLean.Shared.PhysicalFermionPairAnchor TorusLean.Shared.PhysicalFermionNormalSquare
open TorusLean.Shared.RelativeJetMap
open scoped TensorProduct ComplexConjugate BigOperators

/-- Original ordered CAR mode pair, restricted to its proved degree. -/
def exteriorModePair (G : Geometry) (theta : Twist) (N : ℕ) (p : PairIndex G theta) :
    Exterior (Fin (physicalQ G theta+1)) (N+2) →ₗ[ℂ]
      Exterior (Fin (physicalQ G theta+1)) N :=
  exteriorPairAnnihilate (mode p.1) (mode p.2)

@[simp] theorem exteriorModePair_coe (G : Geometry) (theta : Twist) (N : ℕ)
    (p : PairIndex G theta) (x : Exterior (Fin (physicalQ G theta+1)) (N+2)) :
    (exteriorModePair G theta N p x : Space (physicalQ G theta)) =
      modePairAnnihilate (physicalQ G theta) p (x : Space (physicalQ G theta)) := rfl

/-- The complete physical m=1 anchor has the same actual section expansion. -/
theorem exteriorPairAt_section_expansion (G : Geometry) (theta : Twist) (N : ℕ) (R : ℂ)
    (x : Exterior (Fin (physicalQ G theta+1)) (N+2)) :
    exteriorPairAnnihilate (-physicalJetCoordinates G theta 0 R)
      (physicalJetCoordinates G theta 1 R) x =
      ∑ p : PairIndex G theta, (pairSection G theta p).val R •
        exteriorModePair G theta N p x := by
  classical
  apply Subtype.ext
  simp only [Submodule.coe_sum, Submodule.coe_smul, exteriorPairAnnihilate_coe,
    exteriorModePair_coe]
  simpa only [pairAt, LinearMap.sum_apply, LinearMap.smul_apply] using
    LinearMap.congr_fun (pairAt_section_expansion G theta R) (x : Space (physicalQ G theta))

/-- Coefficient at an arbitrary actual spectator configuration. -/
def doubleSpectator (G : Geometry) (theta : Twist) (N : ℕ)
    (x : Exterior (Fin (physicalQ G theta+1)) ((N+2)+2))
    (a b : PairIndex G theta) : Configuration N → ℂ :=
  physicalExteriorLinear G theta N
    (exteriorModePair G theta N b (exteriorModePair G theta (N+2) a x))

/-- Genuine finite tensor in the full LLL₂ ⊗ LLL₂ Hilbert space.
No completeness or tensor-valued representation premise is supplied. -/
def doublePairTensor (G : Geometry) (theta : Twist) (N : ℕ)
    (x : Exterior (Fin (physicalQ G theta+1)) ((N+2)+2)) (z : Configuration N) :
    LLL G theta 2 ⊗[ℂ] LLL G theta 2 :=
  ∑ a : PairIndex G theta, ∑ b : PairIndex G theta,
    doubleSpectator G theta N x a b z •
      (pairSection G theta a ⊗ₜ[ℂ] pairSection G theta b)

theorem doublePairTensor_apply (G : Geometry) (theta : Twist) (N : ℕ)
    (x : Exterior (Fin (physicalQ G theta+1)) ((N+2)+2))
    (z : Configuration N) (R S : ℂ) :
    rawPairFunction G theta 2 2 (doublePairTensor G theta N x z) (R,S) =
      physicalExteriorLinear G theta N
        (exteriorPairAnnihilate (-physicalJetCoordinates G theta 0 S)
          (physicalJetCoordinates G theta 1 S)
          (exteriorPairAnnihilate (-physicalJetCoordinates G theta 0 R)
            (physicalJetCoordinates G theta 1 R) x)) z := by
  classical
  rw [exteriorPairAt_section_expansion G theta (N+2) R x]
  simp only [map_sum, map_smul]
  simp_rw [exteriorPairAt_section_expansion G theta N S]
  simp only [doublePairTensor, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, doubleSpectator, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [rawPairFunction_tmul_apply G theta 2 2 (pairSection G theta a)
    (pairSection G theta b) (R,S)]
  ring

/-- The original normalized pair anchor is applied twice, with every
spectator and the original physical many-body state retained. -/
def physicalDoublePairFunction (G : Geometry) (theta : Twist) (N : ℕ)
    (R S : ℂ) (f : PhysicalFermion G theta ((N+2)+2)) : Configuration N → ℂ :=
  (physicalM1PairSection G theta N S (physicalM1PairSection G theta (N+2) R f)).val

def physicalDoublePairTensor (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta ((N+2)+2)) (z : Configuration N) :
    LLL G theta 2 ⊗[ℂ] LLL G theta 2 :=
  doublePairTensor G theta N ((physicalExteriorEquiv G theta ((N+2)+2)).symm f) z

/-- Pointwise representation of the literal two-contact physical output. -/
theorem physicalDoublePairTensor_apply (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta ((N+2)+2)) (z : Configuration N) (R S : ℂ) :
    rawPairFunction G theta 2 2 (physicalDoublePairTensor G theta N f z) (R,S) =
      physicalDoublePairFunction G theta N R S f z := by
  rw [physicalDoublePairTensor, doublePairTensor_apply]
  unfold physicalDoublePairFunction
  have hR := physicalM1PairSection_intertwine G theta (N+2) R
    ((physicalExteriorEquiv G theta ((N+2)+2)).symm f)
  rw [Equiv.apply_symm_apply] at hR
  rw [hR, physicalM1PairSection_intertwine]
  rfl

/-- The two original pair factors have no extra norm, count or factorial. -/
theorem physicalDoublePairFunction_normSq (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta ((N+2)+2)) (R S : ℂ) :
    (∫ z, ‖physicalDoublePairFunction G theta N R S f z‖^2 ∂sectorMeasure G N) =
      occupationNormSq (physicalQ G theta)
        (pairAt G theta S (pairAt G theta R
          ((physicalExteriorEquiv G theta ((N+2)+2)).symm f : Space (physicalQ G theta)))) := by
  have h := fullCarrier_m1_pair_normSq G theta N S
    (physicalM1PairSection G theta (N+2) R f)
  rw [fullCarrier_m1_pair_CAR] at h
  exact h

#print axioms exteriorPairAt_section_expansion
#print axioms doublePairTensor_apply
#print axioms physicalDoublePairTensor_apply
#print axioms physicalDoublePairFunction_normSq
end TorusLean.Shared.FermionRelativeFrame
