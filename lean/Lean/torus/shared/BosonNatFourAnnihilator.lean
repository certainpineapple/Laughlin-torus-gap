import torus.shared.BosonNatFourRemovalTrace

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatFourAnnihilator
open TorusLean.Boson TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.ThermalCoherentFourBodyLift
open TorusLean.Shared.ThermalCoherentFourBodyFrame
open TorusLean.Shared.BosonAnchoredNatLinearActions TorusLean.Shared.BosonNatFourRemovalTrace
open TorusLean.Shared.BosonNormalizedNatSeeds
open scoped BigOperators ComplexConjugate

local instance natAnnihilator_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

/-- The original ordered-quadruple Parseval annihilator, conjugate linear in
its genuine Nat-polynomial seed. On particle-four seeds it equals the
previously defined physical fourSeedRemoval exactly. -/
def natFourAnnihilator (G : Geometry) (theta : Twist) (R : ℂ) :
    Core ℕ ℂ →ₛₗ[starRingEnd ℂ]
      (Core (OrbitalIndex G theta) ℂ →ₗ[ℂ] Core (OrbitalIndex G theta) ℂ) where
  toFun p := ∑ a, conj (seedDualMapNat G theta (quadVacuum a).val p R) • quadRemove a
  map_add' p q := by
    simp only [map_add,Pi.add_apply,map_add,add_smul,Finset.sum_add_distrib]
  map_smul' c p := by
    simp only [map_smul,Pi.smul_apply,smul_eq_mul,map_mul,Finset.smul_sum,smul_smul]

theorem natFourAnnihilator_normalized (G : Geometry) (theta : Twist) (p : Core ℕ ℂ)
    (hp : p.IsHomogeneous 4) (n : ℕ) (R : ℂ) :
    natFourAnnihilator G theta R (normalizedNatSeed 4 n p) = natFourRemoval G theta p hp n R := by
  apply LinearMap.ext
  intro f
  rw [natFourRemoval_expansion]
  simp only [natFourAnnihilator,LinearMap.coe_mk,AddHom.coe_mk,LinearMap.sum_apply,LinearMap.smul_apply]

theorem natFourAnnihilator_ground (G : Geometry) (theta : Twist) (p : Core ℕ ℂ)
    (hp : p.IsHomogeneous 4) (R : ℂ) :
    natFourAnnihilator G theta R p = natFourRemoval G theta p hp 0 R := by
  simpa only [normalizedNatSeed_zero] using natFourAnnihilator_normalized G theta p hp 0 R

end TorusLean.Shared.BosonNatFourAnnihilator
