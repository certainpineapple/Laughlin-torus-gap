import torus.shared.ThermalCoherentFourBodyFrame

/-! The normalized four-body lift on the existing factorial core. Its
four-particle restriction and reconstruction of every normal-ordered coefficient
operator are proved using the genuine ordered Parseval family. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFourBodyLift
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonThreeBodyLift TorusLean.Shared.ThermalCoherentFourBodyFrame
open scoped BigOperators ComplexConjugate
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def quadCoefficientLift (K : Matrix (QuadIndex ι) (QuadIndex ι) ℂ) :
    Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  ∑ a, ∑ b, K a b • (quadCreate a).comp (quadRemove b)

def fourSectorKernel (A : FourSector ι →ₗ[ℂ] FourSector ι) :
    Matrix (QuadIndex ι) (QuadIndex ι) ℂ :=
  fun a b => ip (quadVacuum a).val (A (quadVacuum b)).val

def fourBodyLift (A : FourSector ι →ₗ[ℂ] FourSector ι) : Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  quadCoefficientLift (fourSectorKernel A)

def fourSeedRankOne (s t : FourSector ι) : FourSector ι →ₗ[ℂ] FourSector ι where
  toFun f := ip t.val f.val • s
  map_add' f g := by
    simp only [Submodule.coe_add, ip, occupationInner_add_right, add_smul]
  map_smul' c f := by
    simp only [Submodule.coe_smul, ip, occupationInner_smul_right, smul_smul]
    rfl

def fourSeedRemoval (s : FourSector ι) : Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  ∑ a, ip s.val (quadVacuum a).val • quadRemove a

theorem fourSeed_creation_resolution (s : FourSector ι) (f : Core ι ℂ) :
    (∑ a, ip (quadVacuum a).val s.val • quadCreate a f) = s.val * f := by
  simp only [quadCreate_eq_vacuum_mul, ← smul_mul_assoc, ← Finset.sum_mul,
    quadVacuum_parseval]

theorem fourSeedRemoval_adjoint (s : FourSector ι) (f p : Core ι ℂ) :
    ip (s.val * f) p = ip f (fourSeedRemoval s p) := by
  rw [← fourSeed_creation_resolution s f]
  simp only [fourSeedRemoval, LinearMap.sum_apply, LinearMap.smul_apply,
    inner_sum_left, inner_sum_right, TwoBodyLift.inner_smul_left, TwoBodyLift.inner_smul_right,
    quadRemove_create_adjoint]
  apply Finset.sum_congr rfl
  intro a ha
  rw [show star (ip (quadVacuum a).val s.val) = ip s.val (quadVacuum a).val from
    occupationInner_conj_symm (fun _ => 1) _ _]

theorem fourBodyLift_fourSeedRankOne_apply (s t : FourSector ι) (p : Core ι ℂ) :
    fourBodyLift (fourSeedRankOne s t) p = s.val * fourSeedRemoval t p := by
  have hrow (x : QuadIndex ι) :
      (∑ y, (ip t.val (quadVacuum y).val * ip (quadVacuum x).val s.val) •
        quadCreate x (quadRemove y p)) =
      ip (quadVacuum x).val s.val • quadCreate x (fourSeedRemoval t p) := by
    simp only [fourSeedRemoval, LinearMap.sum_apply, LinearMap.smul_apply,
      map_sum, map_smul, Finset.smul_sum, smul_smul, mul_comm]
  simp only [fourBodyLift, quadCoefficientLift, fourSectorKernel,
    fourSeedRankOne, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_smul,
    TwoBodyLift.inner_smul_right, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, hrow]
  exact fourSeed_creation_resolution s _

theorem fourSeedRemoval_quadVacuum (a : QuadIndex ι) :
    fourSeedRemoval (quadVacuum a) = quadRemove a := by
  apply LinearMap.ext
  intro p
  apply ip_ext_right
  intro f
  rw [← fourSeedRemoval_adjoint, ← quadCreate_eq_vacuum_mul,
    quadRemove_create_adjoint]

theorem fourBodyLift_rank (a b : QuadIndex ι) :
    fourBodyLift (fourSeedRankOne (quadVacuum a) (quadVacuum b)) =
      (quadCreate a).comp (quadRemove b) := by
  apply LinearMap.ext
  intro p
  rw [fourBodyLift_fourSeedRankOne_apply, fourSeedRemoval_quadVacuum]
  exact (quadCreate_eq_vacuum_mul a _).symm

theorem fourSector_frame (f : FourSector ι) :
    (∑ a, ip (quadVacuum a).val f.val • quadVacuum a) = f := by
  apply Subtype.ext
  simpa only [Submodule.coe_sum, Submodule.coe_smul] using quadVacuum_parseval f

/-- The normalized generic lift restricts to exactly its input operator at N=4. -/
theorem fourBodyLift_fourSector (A : FourSector ι →ₗ[ℂ] FourSector ι)
    (f : FourSector ι) : fourBodyLift A f.val = (A f).val := by
  have hc (a : QuadIndex ι) :
      (∑ b, fourSectorKernel A a b * ip (quadVacuum b).val f.val) =
        ip (quadVacuum a).val (A f).val := by
    conv_rhs => rw [← fourSector_frame f]
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
      inner_sum_right, TwoBodyLift.inner_smul_right, fourSectorKernel, mul_comm]
  simp only [fourBodyLift, quadCoefficientLift, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, quadRemove_fourSector,
    map_smul, smul_smul]
  simp_rw [← Finset.sum_smul, hc]
  exact quadVacuum_parseval (A f)

def fourBodyLiftLinear :
    (FourSector ι →ₗ[ℂ] FourSector ι) →ₗ[ℂ] (Core ι ℂ →ₗ[ℂ] Core ι ℂ) where
  toFun := fourBodyLift
  map_add' A B := by
    ext f
    simp only [fourBodyLift, quadCoefficientLift, fourSectorKernel,
      LinearMap.add_apply, Submodule.coe_add, ip, occupationInner_add_right,
      LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      add_smul, Finset.sum_add_distrib]
  map_smul' c A := by
    ext f
    simp only [fourBodyLift, quadCoefficientLift, fourSectorKernel,
      LinearMap.smul_apply, Submodule.coe_smul, ip, occupationInner_smul_right,
      LinearMap.sum_apply, LinearMap.comp_apply, smul_smul, Finset.smul_sum]
    rfl

/-- The finite four-sector coefficient operator, not a new all-N assumption. -/
def coefficientFourSector (K : Matrix (QuadIndex ι) (QuadIndex ι) ℂ) :
    FourSector ι →ₗ[ℂ] FourSector ι :=
  ∑ a, ∑ b, K a b • fourSeedRankOne (quadVacuum a) (quadVacuum b)

theorem coefficientFourSector_apply (K : Matrix (QuadIndex ι) (QuadIndex ι) ℂ)
    (f : FourSector ι) : (coefficientFourSector K f).val = quadCoefficientLift K f.val := by
  simp only [coefficientFourSector, quadCoefficientLift, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, fourSeedRankOne,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sum, Submodule.coe_smul,
    quadRemove_fourSector, map_smul, smul_smul]
  rfl

/-- Every actual four-body normal order is the normalized lift of its proved
four-particle restriction, including redundant and repeated tensor labels. -/
theorem fourBodyLift_restriction (K : Matrix (QuadIndex ι) (QuadIndex ι) ℂ) :
    fourBodyLift (coefficientFourSector K) = quadCoefficientLift K := by
  change fourBodyLiftLinear (coefficientFourSector K) = _
  simp only [coefficientFourSector, map_sum, map_smul, fourBodyLiftLinear,
    LinearMap.coe_mk, AddHom.coe_mk, fourBodyLift_rank, quadCoefficientLift]

theorem quadCoefficientLift_low_sector (K : Matrix (QuadIndex ι) (QuadIndex ι) ℂ)
    (N : ℕ) (hN : N < 4) (f : Core ι ℂ) (hf : f.IsHomogeneous N) :
    quadCoefficientLift K f = 0 := by
  simp only [quadCoefficientLift, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, quadRemove_low_sector _ N hN f hf,
    map_zero, smul_zero, Finset.sum_const_zero]

theorem fourBodyLift_low_sector (A : FourSector ι →ₗ[ℂ] FourSector ι)
    (N : ℕ) (hN : N < 4) (f : Core ι ℂ) (hf : f.IsHomogeneous N) :
    fourBodyLift A f = 0 := quadCoefficientLift_low_sector _ N hN f hf

theorem quadCoefficientLift_sector (K : Matrix (QuadIndex ι) (QuadIndex ι) ℂ)
    (N : ℕ) (f : Core ι ℂ) (hf : f.IsHomogeneous (N+4)) :
    (quadCoefficientLift K f).IsHomogeneous (N+4) := by
  simp only [quadCoefficientLift, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro a ha
  apply MvPolynomial.IsHomogeneous.sum
  intro b hb
  rw [MvPolynomial.smul_eq_C_mul]
  exact (quadCreate_sector a N _ (quadRemove_sector b N f hf)).C_mul _

theorem fourBodyLift_sector (A : FourSector ι →ₗ[ℂ] FourSector ι)
    (N : ℕ) (f : Core ι ℂ) (hf : f.IsHomogeneous N) :
    (fourBodyLift A f).IsHomogeneous N := by
  by_cases hN : N < 4
  · rw [fourBodyLift_low_sector A N hN f hf]
    exact MvPolynomial.isHomogeneous_zero (σ := ι) (R := ℂ) N
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 4 := ⟨N-4, by omega⟩
    exact quadCoefficientLift_sector _ n f hf

end TorusLean.Shared.ThermalCoherentFourBodyLift
