import torus.shared.BosonNatThreeRemovalTrace

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatThreeAnnihilator
open TorusLean.Boson TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonThreeBodyLift
open TorusLean.Shared.BosonAnchoredNatLinearActions TorusLean.Shared.BosonNatThreeRemovalTrace
open TorusLean.Shared.BosonNormalizedNatSeeds
open scoped BigOperators ComplexConjugate

local instance natAnnihilator_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

/-- The original ordered-triple Parseval annihilator, conjugate linear in
its genuine Nat-polynomial seed. On particle-three seeds it equals the
previously defined physical threeSeedRemoval exactly. -/
def natThreeAnnihilator (G : Geometry) (theta : Twist) (R : ℂ) :
    Core ℕ ℂ →ₛₗ[starRingEnd ℂ]
      (Core (OrbitalIndex G theta) ℂ →ₗ[ℂ] Core (OrbitalIndex G theta) ℂ) where
  toFun p := ∑ a, conj (seedDualMapNat G theta (tripleVacuum a).val p R) • tripleRemove a
  map_add' p q := by
    simp only [map_add,Pi.add_apply,map_add,add_smul,Finset.sum_add_distrib]
  map_smul' c p := by
    simp only [map_smul,Pi.smul_apply,smul_eq_mul,map_mul,Finset.smul_sum,smul_smul]

theorem natThreeAnnihilator_normalized (G : Geometry) (theta : Twist) (p : Core ℕ ℂ)
    (hp : p.IsHomogeneous 3) (n : ℕ) (R : ℂ) :
    natThreeAnnihilator G theta R (normalizedNatSeed 3 n p) = natThreeRemoval G theta p hp n R := by
  apply LinearMap.ext
  intro f
  rw [natThreeRemoval_expansion]
  simp only [natThreeAnnihilator,LinearMap.coe_mk,AddHom.coe_mk,LinearMap.sum_apply,LinearMap.smul_apply]

theorem natThreeAnnihilator_ground (G : Geometry) (theta : Twist) (p : Core ℕ ℂ)
    (hp : p.IsHomogeneous 3) (R : ℂ) :
    natThreeAnnihilator G theta R p = natThreeRemoval G theta p hp 0 R := by
  simpa only [normalizedNatSeed_zero] using natThreeAnnihilator_normalized G theta p hp 0 R

end TorusLean.Shared.BosonNatThreeAnnihilator
