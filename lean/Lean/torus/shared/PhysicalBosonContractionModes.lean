import torus.shared.PhysicalBosonContractionIntegral

/-! Exact moving-mode CCR, with nonorthogonal physical modes allowed. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.PhysicalBosonContractionModes
open TorusLean.Boson TorusLean.Boson.UnitaryTransport
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mode_pair_raw_normal_order (u v : Orbital ι) (f : Core ι ℂ) :
    modeAnnihilate u (modeAnnihilate u (modeCreate v (modeCreate v f))) =
      modeCreate v (modeCreate v (modeAnnihilate u (modeAnnihilate u f))) +
      (4*inner ℂ u v) • modeCreate v (modeAnnihilate u f) +
      (2*(inner ℂ u v)^2) • f := by
  simp only [mode_mixed_ccr, map_add, map_smul, smul_add, smul_smul]
  module

def modePairCreate (u : Orbital ι) : Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (modeCreate u).comp (modeCreate u)

theorem mode_pair_normal_order (u v : Orbital ι) (f : Core ι ℂ) :
    modePair u (modePairCreate v f) = modePairCreate v (modePair u f) +
      (2*inner ℂ u v) • modeCreate v (modeAnnihilate u f) +
      (inner ℂ u v)^2 • f := by
  have hs : ((Real.sqrt 2)⁻¹ : ℂ)*((Real.sqrt 2)⁻¹ : ℂ) = (1/2:ℂ) := by
    rw [←pow_two,inv_pow,←Complex.ofReal_pow,Real.sq_sqrt (by norm_num)]
    norm_num
  simp only [modePair,modePairCreate,LinearMap.smul_apply,LinearMap.comp_apply,
    map_smul,smul_smul,hs,mode_pair_raw_normal_order,smul_add]
  simp only [smul_smul,←mul_assoc,hs]
  module

end TorusLean.Shared.PhysicalBosonContractionModes
