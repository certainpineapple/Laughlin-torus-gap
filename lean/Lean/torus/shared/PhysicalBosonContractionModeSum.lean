import torus.shared.PhysicalBosonContractionModes
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.PhysicalBosonContractionModes
open TorusLean.Boson TorusLean.Boson.UnitaryTransport
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The original four ordered single CCR coefficients collapse to the actual
nonorthogonal one-particle Gram. No canonical-mode orthogonality is assumed. -/
theorem singleContraction_mode_sum (u v : Orbital ι) (f : Core ι ℂ) [Nonempty ι] :
    (∑ b : TwoBodyLift.PairIndex ι, ∑ c : TwoBodyLift.PairIndex ι,
      (star (u b.1) * star (u b.2) * (v c.1 * v c.2)) •
        TorusLean.Shared.BosonPairContractions.singleContraction b c f) =
      (2*inner ℂ u v) • modeCreate v (modeAnnihilate u f) := by
  classical
  have hs : ((Real.sqrt 2)⁻¹ : ℂ)^2 = (1/2:ℂ) := by
    rw [inv_pow,←Complex.ofReal_pow,Real.sq_sqrt (by norm_num)]
    norm_num
  simp only [TorusLean.Shared.BosonPairContractions.singleContraction, hs,
    LinearMap.smul_apply, LinearMap.add_apply, smul_add, smul_smul, Finset.sum_add_distrib,
    Fintype.sum_prod_type]
  have hite (P : Prop) [Decidable P] (T : Core ι ℂ →ₗ[ℂ] Core ι ℂ) :
      (if P then T else 0) f = if P then T f else 0 := by split_ifs <;> rfl
  simp only [hite, LinearMap.comp_apply,
    smul_ite, smul_zero]
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [modeCreate,modeAnnihilate,LinearMap.sum_apply,LinearMap.smul_apply,
    map_sum,map_smul,Finset.smul_sum,smul_smul,PiLp.inner_apply,RCLike.inner_apply,
    Finset.sum_mul,Finset.mul_sum,Finset.sum_smul]
  conv_lhs => arg 1; arg 2; rw [Finset.sum_comm]
  conv_lhs => arg 2; rw [Finset.sum_comm]
  conv_rhs => arg 2; ext x; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  simp only [starRingEnd_apply]
  module

end TorusLean.Shared.PhysicalBosonContractionModes
