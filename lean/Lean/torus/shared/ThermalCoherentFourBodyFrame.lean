import torus.shared.BosonThreeBodyLift

/-! The ordered four-orbital Parseval family in the unchanged factorial core.
Every label, including repeated modes, is retained. Creation and removal use
exactly 1/sqrt(4!), as independently verified by the degree-four Euler identity. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFourBodyFrame
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonThreeBodyLift
open scoped BigOperators ComplexConjugate
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

abbrev QuadIndex (ι : Type*) := (ι × ι) × (ι × ι)
abbrev FourSector (ι : Type*) := MvPolynomial.homogeneousSubmodule ι ℂ 4

def quadCreate (a : QuadIndex ι) : Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  ((Real.sqrt 24)⁻¹ : ℂ) • (create a.1.1).comp
    ((create a.1.2).comp ((create a.2.1).comp (create a.2.2)))

def quadRemove (a : QuadIndex ι) : Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  ((Real.sqrt 24)⁻¹ : ℂ) • (annihilate a.2.2).comp
    ((annihilate a.2.1).comp ((annihilate a.1.2).comp (annihilate a.1.1)))

theorem quadCreate_remove_adjoint (a : QuadIndex ι) (f g : Core ι ℂ) :
    ip f (quadCreate a g) = ip (quadRemove a f) g := by
  simp only [quadCreate, quadRemove, LinearMap.smul_apply, LinearMap.comp_apply,
    ip, occupationInner_smul_left, occupationInner_smul_right,
    ← annihilate_adjoint_canonical]
  simp [Complex.star_def]

theorem quadRemove_create_adjoint (a : QuadIndex ι) (f g : Core ι ℂ) :
    ip (quadCreate a f) g = ip f (quadRemove a g) := by
  simp only [quadCreate, quadRemove, LinearMap.smul_apply, LinearMap.comp_apply,
    ip, occupationInner_smul_left, occupationInner_smul_right, create_adjoint_canonical]
  simp

theorem quadRemove_sector (a : QuadIndex ι) (N : ℕ) (f : Core ι ℂ)
    (hf : f.IsHomogeneous (N + 4)) : (quadRemove a f).IsHomogeneous N := by
  have h1 := TorusLean.BosonBridge.OccupationInstance.annihilate_sector
    (N+3) a.1.1 f (by simpa only [Nat.add_assoc] using hf)
  have h2 := TorusLean.BosonBridge.OccupationInstance.annihilate_sector
    (N+2) a.1.2 _ (by simpa only [Nat.add_assoc] using h1)
  have h3 := TorusLean.BosonBridge.OccupationInstance.annihilate_sector
    (N+1) a.2.1 _ (by simpa only [Nat.add_assoc] using h2)
  have h4 := TorusLean.BosonBridge.OccupationInstance.annihilate_sector N a.2.2 _ h3
  simp only [quadRemove, LinearMap.smul_apply, LinearMap.comp_apply,
    MvPolynomial.smul_eq_C_mul]
  exact h4.C_mul _

theorem quadCreate_sector (a : QuadIndex ι) (N : ℕ) (f : Core ι ℂ)
    (hf : f.IsHomogeneous N) : (quadCreate a f).IsHomogeneous (N + 4) := by
  have h1 := (MvPolynomial.isHomogeneous_X ℂ a.2.2).mul hf
  have h2 := (MvPolynomial.isHomogeneous_X ℂ a.2.1).mul h1
  have h3 := (MvPolynomial.isHomogeneous_X ℂ a.1.2).mul h2
  have h4 := (MvPolynomial.isHomogeneous_X ℂ a.1.1).mul h3
  simp only [quadCreate, LinearMap.smul_apply, LinearMap.comp_apply, create,
    LinearMap.mulLeft_apply, MvPolynomial.smul_eq_C_mul]
  convert h4.C_mul ((Real.sqrt 24)⁻¹ : ℂ) using 1 <;> omega

def quadVacuum (a : QuadIndex ι) : FourSector ι :=
  ⟨quadCreate a 1, quadCreate_sector a 0 1 (MvPolynomial.isHomogeneous_one ι ℂ)⟩

theorem quadCreate_eq_vacuum_mul (a : QuadIndex ι) (f : Core ι ℂ) :
    quadCreate a f = (quadVacuum a).val * f := by
  simp [quadVacuum, quadCreate, create, MvPolynomial.smul_eq_C_mul, mul_assoc]

theorem quadRemove_fourSector (a : QuadIndex ι) (f : FourSector ι) :
    quadRemove a f.val = ip (quadVacuum a).val f.val • (1 : Core ι ℂ) := by
  rw [homogeneous_zero_eq_vacuum _ (quadRemove_sector a 0 f.val f.property)]
  rw [← quadRemove_create_adjoint]
  rfl

theorem euler_four (f : FourSector ι) :
    (∑ i, ∑ j, ∑ k, ∑ l, create i (create j (create k (create l
      (annihilate l (annihilate k (annihilate j (annihilate i f.val)))))))) =
        (24 : ℂ) • f.val := by
  have hi (i : ι) := TorusLean.BosonBridge.OccupationInstance.annihilate_sector
    3 i f.val f.property
  have hij (i j : ι) := TorusLean.BosonBridge.OccupationInstance.annihilate_sector
    2 j _ (hi i)
  have hijk (i j k : ι) := TorusLean.BosonBridge.OccupationInstance.annihilate_sector
    1 k _ (hij i j)
  simp_rw [← map_sum, euler_one 1 _ (hijk _ _ _), one_nsmul,
    euler_one 2 _ (hij _ _), map_nsmul, ← Finset.smul_sum,
    euler_one 3 _ (hi _), map_nsmul, ← Finset.smul_sum,
    euler_one 4 f.val f.property]
  norm_num [nsmul_eq_mul, MvPolynomial.smul_eq_C_mul, map_ofNat]
  ring

theorem quadResolution (f : FourSector ι) :
    (∑ a : QuadIndex ι, quadCreate a (quadRemove a f.val)) = f.val := by
  have hs : (((Real.sqrt 24)⁻¹ : ℂ) * ((Real.sqrt 24)⁻¹ : ℂ)) = (24 : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  simp only [quadCreate, quadRemove, LinearMap.smul_apply, LinearMap.comp_apply,
    map_smul, smul_smul, hs, Fintype.sum_prod_type]
  simp_rw [← Finset.smul_sum]
  rw [euler_four, smul_smul]
  norm_num

theorem quadVacuum_parseval (f : FourSector ι) :
    (∑ a : QuadIndex ι, ip (quadVacuum a).val f.val • (quadVacuum a).val) = f.val := by
  have h := quadResolution f
  simpa only [quadRemove_fourSector, map_smul, quadVacuum] using h

theorem quadRemove_low_sector (a : QuadIndex ι) (N : ℕ) (hN : N < 4)
    (f : Core ι ℂ) (hf : f.IsHomogeneous N) : quadRemove a f = 0 := by
  simp only [quadRemove, LinearMap.smul_apply, LinearMap.comp_apply]
  rcases N with _ | _ | _ | _ | N
  · rw [annihilate_homogeneous_zero a.1.1 f hf, map_zero, map_zero, map_zero, smul_zero]
  · have h1 := TorusLean.BosonBridge.OccupationInstance.annihilate_sector 0 a.1.1 f hf
    rw [annihilate_homogeneous_zero a.1.2 _ h1, map_zero, map_zero, smul_zero]
  · have h1 := TorusLean.BosonBridge.OccupationInstance.annihilate_sector 1 a.1.1 f hf
    have h2 := TorusLean.BosonBridge.OccupationInstance.annihilate_sector 0 a.1.2 _ h1
    rw [annihilate_homogeneous_zero a.2.1 _ h2, map_zero, smul_zero]
  · have h1 := TorusLean.BosonBridge.OccupationInstance.annihilate_sector 2 a.1.1 f hf
    have h2 := TorusLean.BosonBridge.OccupationInstance.annihilate_sector 1 a.1.2 _ h1
    have h3 := TorusLean.BosonBridge.OccupationInstance.annihilate_sector 0 a.2.1 _ h2
    rw [annihilate_homogeneous_zero a.2.2 _ h3, smul_zero]
  · omega

/-- The normalization matches the existing double-pair normal order exactly.
The factor six is 4!/(2! 2!), and is unrelated to any COM Jacobian. -/
theorem doublePair_eq_six_quad (a b c d : PairIndex ι) (f : Core ι ℂ) :
    pairCreate a (pairCreate c (pairRemove d (pairRemove b f))) =
      (6 : ℂ) • quadCreate (a,c) (quadRemove (b,d) f) := by
  have hs2 : (((Real.sqrt 2)⁻¹ : ℂ))^2 = (1/2 : ℂ) := by
    rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hs24 : (((Real.sqrt 24)⁻¹ : ℂ))^2 = (1/24 : ℂ) := by
    rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  simp only [pairCreate, pairRemove, quadCreate, quadRemove,
    LinearMap.smul_apply, LinearMap.comp_apply, map_smul, smul_smul]
  congr 1
  calc
    _ = (((Real.sqrt 2)⁻¹ : ℂ))^2 * (((Real.sqrt 2)⁻¹ : ℂ))^2 := by ring
    _ = 6 * (((Real.sqrt 24)⁻¹ : ℂ) * ((Real.sqrt 24)⁻¹ : ℂ)) := by
      rw [hs2, ← pow_two (((Real.sqrt 24)⁻¹ : ℂ)), hs24]
      norm_num

#print axioms quadCreate_remove_adjoint
#print axioms quadRemove_create_adjoint
#print axioms quadRemove_sector
#print axioms quadCreate_sector
#print axioms quadCreate_eq_vacuum_mul
#print axioms quadRemove_fourSector
#print axioms euler_four
#print axioms quadResolution
#print axioms quadVacuum_parseval
#print axioms quadRemove_low_sector
#print axioms doublePair_eq_six_quad
end TorusLean.Shared.ThermalCoherentFourBodyFrame
