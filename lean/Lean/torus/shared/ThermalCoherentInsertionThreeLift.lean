import torus.shared.BosonThreeBodyLift
import torus.shared.ThermalCoherentInsertionPhysical

/-! The existing ordered-triple lift of an actual inserted rank-one seed.
The Parseval resolution proves the all-core identification; no lifting identity
is assumed. COM averaging and the infinite thermal transfer remain separate. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentInsertionThreeLift
open TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Boson.SpectatorControl TorusLean.Boson.Sym2Evaluation
open TorusLean.Shared.BosonThreeBodyLift
open TorusLean.Shared.ThermalCoherentInsertionAlgebra
open TorusLean.Shared.ThermalCoherentInsertionPhysical
open scoped TensorProduct ComplexConjugate

section Algebra
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The rank-one map of the actual three-particle seed in the original metric. -/
def threeSeedRankOne (s : ThreeSector ι) : ThreeSector ι →ₗ[ℂ] ThreeSector ι where
  toFun f := ip s.val f.val • s
  map_add' f g := by
    simp only [Submodule.coe_add, ip, occupationInner_add_right, add_smul]
  map_smul' c f := by
    simp only [Submodule.coe_smul, ip, occupationInner_smul_right, smul_smul]
    rfl

/-- Actual Parseval annihilation row, including every ordered repeated triple. -/
def threeSeedRemoval (s : ThreeSector ι) : Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  ∑ a, ip s.val (tripleVacuum a).val • tripleRemove a

theorem threeSeed_creation_resolution (s : ThreeSector ι) (f : Core ι ℂ) :
    (∑ a, ip (tripleVacuum a).val s.val • tripleCreate a f) = s.val * f := by
  simp only [tripleCreate_eq_vacuum_mul, ← smul_mul_assoc, ← Finset.sum_mul,
    tripleVacuum_parseval]

theorem threeSeedRemoval_adjoint (s : ThreeSector ι) (f p : Core ι ℂ) :
    ip (s.val * f) p = ip f (threeSeedRemoval s p) := by
  rw [← threeSeed_creation_resolution s f]
  simp only [threeSeedRemoval, LinearMap.sum_apply, LinearMap.smul_apply,
    TwoBodyLift.inner_sum_left, TwoBodyLift.inner_sum_right,
    TwoBodyLift.inner_smul_left, TwoBodyLift.inner_smul_right,
    tripleRemove_create_adjoint]
  apply Finset.sum_congr rfl
  intro a ha
  rw [show star (ip (tripleVacuum a).val s.val) = ip s.val (tripleVacuum a).val from
    occupationInner_conj_symm (fun _ => 1) _ _]

/-- The project's existing generic three-body lift equals seed creation times
its derived annihilation row, on the whole core and with its original factors. -/
theorem threeBodyLift_threeSeedRankOne_apply (s : ThreeSector ι) (p : Core ι ℂ) :
    threeBodyLift (threeSeedRankOne s) p = s.val * threeSeedRemoval s p := by
  have hrow (x : TripleIndex ι) :
      (∑ y, (ip s.val (tripleVacuum y).val * ip (tripleVacuum x).val s.val) •
        tripleCreate x (tripleRemove y p)) =
      ip (tripleVacuum x).val s.val • tripleCreate x (threeSeedRemoval s p) := by
    simp only [threeSeedRemoval, LinearMap.sum_apply, LinearMap.smul_apply,
      map_sum, map_smul, Finset.smul_sum, smul_smul, mul_comm]
  simp only [threeBodyLift, tripleCoefficientLift, threeSectorKernel,
    threeSeedRankOne, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_smul,
    TwoBodyLift.inner_smul_right, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, hrow]
  exact threeSeed_creation_resolution s _

def coherentThreeSector (u v : Orbital ι) : ThreeSector ι :=
  ⟨threeInsertion (symTensor u u ⊗ₜ[ℂ] v), threeInsertion_sector _⟩

theorem threeSeedRemoval_coherent (u v : Orbital ι) :
    threeSeedRemoval (coherentThreeSector u v) = (modeAnnihilate v).comp (modePair u) := by
  apply LinearMap.ext
  intro p
  apply ip_ext_right
  intro f
  rw [← threeSeedRemoval_adjoint]
  exact threeInsertion_coherent_adjoint u v f p

/-- Genuine equality to the prior generic L3, not merely its few-body restriction. -/
theorem threeBodyLift_coherent_rankOne (u v : Orbital ι) :
    threeBodyLift (threeSeedRankOne (coherentThreeSector u v)) = coherentThreeLift u v := by
  apply LinearMap.ext
  intro p
  rw [threeBodyLift_threeSeedRankOne_apply, threeSeedRemoval_coherent]
  rfl

end Algebra

open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.ThermalCoherentGaussian TorusLean.Shared.ThermalCoherentIntegral
open TorusLean.Shared.PhysicalBosonPolarization TorusLean.Shared.PhysicalBosonMembership

local instance physicalOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0, lll_finrank_pos G theta 1⟩⟩

theorem coherentThreeSector_eq_physicalSeed (G : Geometry) (theta : Twist) (R S : ℂ) :
    coherentThreeSector (evaluationCoordinates G theta R) (evaluationCoordinates G theta S) =
      (physicalSectorEquiv G theta 3).symm (physicalThreeInsertionSeed G theta R S) := by
  apply Subtype.ext
  exact (physicalThreeInsertionSeed_coordinates G theta R S).symm

/-- The same positive thermal integrand is the quadratic form of the project's
prior generic three-body lift of the actual coherent insertion seed. -/
theorem oneSpectatorIntegrand_eq_threeBodyLift (G : Geometry) (theta : Twist) (a : ℝ)
    (p : Core (OrbitalIndex G theta) ℂ) (x : ℂ × ℂ) :
    oneSpectatorIntegrand G theta a p x = thermalWeight a x.2 *
      (occupationInner (fun _ => 1) p
        (threeBodyLift (threeSeedRankOne (coherentThreeSector
          (evaluationCoordinates G theta x.1)
          (evaluationCoordinates G theta (x.1+x.2)))) p)).re := by
  rw [threeBodyLift_coherent_rankOne]
  exact oneSpectatorIntegrand_eq_coherentLift G theta a p x

/-- In particular the rank-one input is the previously constructed seed in
 the independent full physical three-particle carrier. -/
theorem oneSpectatorIntegrand_eq_physicalThreeBodyLift (G : Geometry) (theta : Twist) (a : ℝ)
    (p : Core (OrbitalIndex G theta) ℂ) (x : ℂ × ℂ) :
    oneSpectatorIntegrand G theta a p x = thermalWeight a x.2 *
      (occupationInner (fun _ => 1) p
        (threeBodyLift (threeSeedRankOne ((physicalSectorEquiv G theta 3).symm
          (physicalThreeInsertionSeed G theta x.1 (x.1+x.2)))) p)).re := by
  rw [← coherentThreeSector_eq_physicalSeed]
  exact oneSpectatorIntegrand_eq_threeBodyLift G theta a p x

#print axioms coherentThreeSector_eq_physicalSeed
#print axioms oneSpectatorIntegrand_eq_physicalThreeBodyLift
#print axioms threeSeed_creation_resolution
#print axioms threeSeedRemoval_adjoint
#print axioms threeBodyLift_threeSeedRankOne_apply
#print axioms threeSeedRemoval_coherent
#print axioms threeBodyLift_coherent_rankOne
#print axioms oneSpectatorIntegrand_eq_threeBodyLift
end TorusLean.Shared.ThermalCoherentInsertionThreeLift
