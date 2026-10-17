import torus.shared.BosonLiftSquare
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonThreeBodyLift
open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonPairContractions TorusLean.Shared.BosonLiftSquare
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- Ordered triples, with no distinctness restriction. -/
abbrev TripleIndex (ι : Type*) := ι × ι × ι
abbrev ThreeSector (ι : Type*) := MvPolynomial.homogeneousSubmodule ι ℂ 3

/-- Exactly the ordered-tensor convention 1/sqrt(3!), including repeated modes. -/
def tripleCreate (a : TripleIndex ι) : Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  ((Real.sqrt 6)⁻¹ : ℂ) •
    (create a.1).comp ((create a.2.1).comp (create a.2.2))

def tripleRemove (a : TripleIndex ι) : Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  ((Real.sqrt 6)⁻¹ : ℂ) •
    (annihilate a.2.2).comp ((annihilate a.2.1).comp (annihilate a.1))

def tripleCoefficientLift (K : Matrix (TripleIndex ι) (TripleIndex ι) ℂ) :
    Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  ∑ a, ∑ b, K a b • (tripleCreate a).comp (tripleRemove b)

theorem tripleCreate_remove_adjoint (a : TripleIndex ι) (f g : Core ι ℂ) :
    ip f (tripleCreate a g) = ip (tripleRemove a f) g := by
  simp only [tripleCreate, tripleRemove, LinearMap.smul_apply, LinearMap.comp_apply,
    ip, occupationInner_smul_left, occupationInner_smul_right,
    ← annihilate_adjoint_canonical]
  simp [Complex.star_def]

theorem tripleRemove_create_adjoint (a : TripleIndex ι) (f g : Core ι ℂ) :
    ip (tripleCreate a f) g = ip f (tripleRemove a g) := by
  simp only [tripleCreate, tripleRemove, LinearMap.smul_apply, LinearMap.comp_apply,
    ip, occupationInner_smul_left, occupationInner_smul_right, create_adjoint_canonical]
  simp

theorem tripleRemove_sector (a : TripleIndex ι) (N : ℕ) (f : Core ι ℂ)
    (hf : f.IsHomogeneous (N + 3)) : (tripleRemove a f).IsHomogeneous N := by
  have h1 := TorusLean.BosonBridge.OccupationInstance.annihilate_sector
    (N + 2) a.1 f (by simpa only [Nat.add_assoc] using hf)
  have h2 := TorusLean.BosonBridge.OccupationInstance.annihilate_sector
    (N + 1) a.2.1 _ (by simpa only [Nat.add_assoc] using h1)
  have h3 := TorusLean.BosonBridge.OccupationInstance.annihilate_sector N a.2.2 _ h2
  simp only [tripleRemove, LinearMap.smul_apply, LinearMap.comp_apply,
    MvPolynomial.smul_eq_C_mul]
  exact h3.C_mul _

theorem tripleCreate_sector (a : TripleIndex ι) (N : ℕ) (f : Core ι ℂ)
    (hf : f.IsHomogeneous N) : (tripleCreate a f).IsHomogeneous (N + 3) := by
  have h1 := (MvPolynomial.isHomogeneous_X ℂ a.2.2).mul hf
  have h2 := (MvPolynomial.isHomogeneous_X ℂ a.2.1).mul h1
  have h3 := (MvPolynomial.isHomogeneous_X ℂ a.1).mul h2
  simp only [tripleCreate, LinearMap.smul_apply, LinearMap.comp_apply, create,
    LinearMap.mulLeft_apply, MvPolynomial.smul_eq_C_mul]
  convert h3.C_mul ((Real.sqrt 6)⁻¹ : ℂ) using 1 <;> omega

def tripleVacuum (a : TripleIndex ι) : ThreeSector ι :=
  ⟨tripleCreate a 1, tripleCreate_sector a 0 1 (MvPolynomial.isHomogeneous_one ι ℂ)⟩

theorem tripleCreate_eq_vacuum_mul (a : TripleIndex ι) (f : Core ι ℂ) :
    tripleCreate a f = (tripleVacuum a).val * f := by
  simp [tripleVacuum, tripleCreate, create, MvPolynomial.smul_eq_C_mul, mul_assoc]

theorem tripleRemove_threeSector (a : TripleIndex ι) (f : ThreeSector ι) :
    tripleRemove a f.val = ip (tripleVacuum a).val f.val • (1 : Core ι ℂ) := by
  rw [homogeneous_zero_eq_vacuum _ (tripleRemove_sector a 0 f.val f.property)]
  rw [← tripleRemove_create_adjoint]
  rfl

def tripleOutputSupport (f : Core ι ℂ) : Finset (ι →₀ ℕ) :=
  Finset.univ.biUnion fun a : TripleIndex ι => (tripleRemove a f).support

theorem tripleRemove_support_subset (f : Core ι ℂ) (a : TripleIndex ι) :
    (tripleRemove a f).support ⊆ tripleOutputSupport f := by
  intro m hm
  exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, hm⟩

theorem tripleCoefficientLift_inner (K : Matrix (TripleIndex ι) (TripleIndex ι) ℂ)
    (f g : Core ι ℂ) :
    ip f (tripleCoefficientLift K g) =
      ∑ a, ∑ b, K a b * ip (tripleRemove a f) (tripleRemove b g) := by
  simp only [tripleCoefficientLift, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, inner_sum_right, TwoBodyLift.inner_smul_right, tripleCreate_remove_adjoint]

theorem tripleCoefficientLift_inner_coefficients
    (K : Matrix (TripleIndex ι) (TripleIndex ι) ℂ) (f : Core ι ℂ) :
    ip f (tripleCoefficientLift K f) = ∑ m ∈ tripleOutputSupport f,
      (occupationMetricWeight (fun _ : ι => 1) m : ℂ) *
        (star (fun a => (tripleRemove a f).coeff m) ⬝ᵥ
          (K *ᵥ (fun a => (tripleRemove a f).coeff m))) := by
  rw [tripleCoefficientLift_inner]
  simp_rw [inner_supported (tripleOutputSupport f) _ _ (tripleRemove_support_subset f _),
    Finset.mul_sum]
  conv_lhs =>
    arg 2
    ext a
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  simp only [Pi.star_apply]
  ring

theorem tripleCoefficientLift_nonneg
    (K : Matrix (TripleIndex ι) (TripleIndex ι) ℂ) (hK : K.PosSemidef)
    (f : Core ι ℂ) : 0 ≤ (ip f (tripleCoefficientLift K f)).re := by
  rw [tripleCoefficientLift_inner_coefficients]
  change 0 ≤ (∑ m ∈ tripleOutputSupport f,
    (occupationMetricWeight (fun _ : ι => 1) m : ℂ) *
      (star (fun a => (tripleRemove a f).coeff m) ⬝ᵥ
        (K *ᵥ (fun a => (tripleRemove a f).coeff m)))).re
  have h := coefficientLiftForm_nonneg (tripleOutputSupport f)
    (fun m => (occupationMetricWeight (fun _ : ι => 1) m : ℝ)) K
    (fun a m => (tripleRemove a f).coeff m) (fun m _ => Nat.cast_nonneg _) hK
  simpa only [coefficientLiftForm, Complex.re_sum, Complex.mul_re,
    Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] using h

theorem euler_one (N : ℕ) (f : Core ι ℂ) (hf : f.IsHomogeneous N) :
    (∑ i, create i (annihilate i f)) = N • f := by
  exact hf.sum_X_mul_pderiv

theorem euler_three (f : ThreeSector ι) :
    (∑ i, ∑ j, ∑ k, create i (create j (create k
      (annihilate k (annihilate j (annihilate i f.val)))))) = (6 : ℂ) • f.val := by
  have hi (i : ι) := TorusLean.BosonBridge.OccupationInstance.annihilate_sector
    2 i f.val f.property
  have hij (i j : ι) := TorusLean.BosonBridge.OccupationInstance.annihilate_sector
    1 j _ (hi i)
  simp_rw [← map_sum, euler_one 1 _ (hij _ _), one_nsmul,
    euler_one 2 _ (hi _), map_nsmul, ← Finset.smul_sum,
    euler_one 3 f.val f.property]
  norm_num [nsmul_eq_mul, MvPolynomial.smul_eq_C_mul, map_ofNat]
  ring

theorem tripleResolution (f : ThreeSector ι) :
    (∑ a : TripleIndex ι, tripleCreate a (tripleRemove a f.val)) = f.val := by
  have hs : (((Real.sqrt 6)⁻¹ : ℂ) * ((Real.sqrt 6)⁻¹ : ℂ)) = (6 : ℂ)⁻¹ := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  simp only [tripleCreate, tripleRemove, LinearMap.smul_apply, LinearMap.comp_apply,
    map_smul, smul_smul, hs, Fintype.sum_prod_type]
  simp_rw [← Finset.smul_sum]
  rw [euler_three, smul_smul]
  norm_num

theorem tripleVacuum_parseval (f : ThreeSector ι) :
    (∑ a : TripleIndex ι, ip (tripleVacuum a).val f.val • (tripleVacuum a).val) = f.val := by
  have h := tripleResolution f
  simpa only [tripleRemove_threeSector, map_smul, tripleVacuum] using h


/-- The coefficient kernel of an actual degree-three operator in the redundant
ordered-triple Parseval family, with its original occupation metric. -/
def threeSectorKernel (A : ThreeSector ι →ₗ[ℂ] ThreeSector ι) :
    Matrix (TripleIndex ι) (TripleIndex ι) ℂ :=
  fun a b => ip (tripleVacuum a).val (A (tripleVacuum b)).val

def threeSectorSynthesis (x : TripleIndex ι → ℂ) : ThreeSector ι :=
  ∑ a, x a • tripleVacuum a

theorem threeSectorKernel_form (A : ThreeSector ι →ₗ[ℂ] ThreeSector ι)
    (x : TripleIndex ι → ℂ) :
    star x ⬝ᵥ (threeSectorKernel A *ᵥ x) =
      ip (threeSectorSynthesis x).val (A (threeSectorSynthesis x)).val := by
  simp only [threeSectorSynthesis, map_sum, map_smul,
    Submodule.coe_sum, Submodule.coe_smul, inner_sum_left, inner_sum_right,
    TwoBodyLift.inner_smul_left, TwoBodyLift.inner_smul_right,
    threeSectorKernel, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- A genuine PSD three-particle form gives a PSD compressed coefficient matrix.
No injectivity of the redundant ordered-triple synthesis map is assumed. -/
theorem threeSectorKernel_posSemidef (A : ThreeSector ι →ₗ[ℂ] ThreeSector ι)
    (hA : ∀ p : ThreeSector ι, 0 ≤ ip p.val (A p).val)
    (hAs : ∀ p q : ThreeSector ι, ip (A p).val q.val = ip p.val (A q).val) :
    (threeSectorKernel A).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext a b
    change star (ip (tripleVacuum b).val (A (tripleVacuum a)).val) = _
    rw [show star (ip (tripleVacuum b).val (A (tripleVacuum a)).val) =
      ip (A (tripleVacuum a)).val (tripleVacuum b).val from
      (occupationInner_conj_symm (fun _ => 1) _ _)]
    exact hAs _ _
  · intro x
    rw [threeSectorKernel_form]
    exact hA _

/-- The normalized three-body lift of an actual finite three-particle operator. -/
def threeBodyLift (A : ThreeSector ι →ₗ[ℂ] ThreeSector ι) :
    Core ι ℂ →ₗ[ℂ] Core ι ℂ := tripleCoefficientLift (threeSectorKernel A)

/-- Three-particle real quadratic nonnegativity lifts to every finite polynomial,
without asking for a global-N bound or using QQ-adjoint near-projectivity. -/
theorem threeBodyLift_nonneg (A : ThreeSector ι →ₗ[ℂ] ThreeSector ι)
    (hA : ∀ p : ThreeSector ι, 0 ≤ (ip p.val (A p).val).re)
    (f : Core ι ℂ) : 0 ≤ (ip f (threeBodyLift A f)).re := by
  rw [threeBodyLift, tripleCoefficientLift_inner_coefficients]
  simp only [Complex.re_sum, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero, threeSectorKernel_form]
  apply Finset.sum_nonneg
  intro m hm
  exact mul_nonneg (Nat.cast_nonneg _) (hA _)

theorem threeSectorKernel_sub (A B : ThreeSector ι →ₗ[ℂ] ThreeSector ι) :
    threeSectorKernel (A - B) = threeSectorKernel A - threeSectorKernel B := by
  ext a b
  change ip (tripleVacuum a).val ((A (tripleVacuum b)).val - (B (tripleVacuum b)).val) =
    ip (tripleVacuum a).val (A (tripleVacuum b)).val -
      ip (tripleVacuum a).val (B (tripleVacuum b)).val
  rw [sub_eq_add_neg, ← neg_one_smul ℂ (B (tripleVacuum b)).val]
  simp only [ip, occupationInner_add_right, occupationInner_smul_right,
    neg_one_mul, sub_eq_add_neg]

theorem tripleCoefficientLift_sub (K L : Matrix (TripleIndex ι) (TripleIndex ι) ℂ) :
    tripleCoefficientLift (K - L) = tripleCoefficientLift K - tripleCoefficientLift L := by
  ext f
  simp only [tripleCoefficientLift, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.sub_apply, Matrix.sub_apply,
    sub_smul, Finset.sum_sub_distrib]

theorem threeBodyLift_sub (A B : ThreeSector ι →ₗ[ℂ] ThreeSector ι) :
    threeBodyLift (A - B) = threeBodyLift A - threeBodyLift B := by
  simp only [threeBodyLift, threeSectorKernel_sub, tripleCoefficientLift_sub]

theorem threeBodyLift_mono (A B : ThreeSector ι →ₗ[ℂ] ThreeSector ι)
    (hAB : ∀ p : ThreeSector ι, (ip p.val (A p).val).re ≤ (ip p.val (B p).val).re)
    (f : Core ι ℂ) : (ip f (threeBodyLift A f)).re ≤ (ip f (threeBodyLift B f)).re := by
  have hsub (p : Core ι ℂ) (g k : Core ι ℂ) : ip p (g - k) = ip p g - ip p k := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ k]
    simp only [ip, occupationInner_add_right, occupationInner_smul_right,
      neg_one_mul, sub_eq_add_neg]
  have h := threeBodyLift_nonneg (B - A) (fun p => by
    simpa only [LinearMap.sub_apply, Submodule.coe_sub, hsub, Complex.sub_re,
      sub_nonneg] using hAB p) f
  rw [threeBodyLift_sub, LinearMap.sub_apply, hsub, Complex.sub_re] at h
  exact sub_nonneg.mp h

theorem threeSector_frame (f : ThreeSector ι) :
    (∑ a, ip (tripleVacuum a).val f.val • tripleVacuum a) = f := by
  apply Subtype.ext
  simpa only [Submodule.coe_sum, Submodule.coe_smul] using tripleVacuum_parseval f

theorem threeBodyLift_threeSector (A : ThreeSector ι →ₗ[ℂ] ThreeSector ι)
    (f : ThreeSector ι) : threeBodyLift A f.val = (A f).val := by
  have hc (a : TripleIndex ι) :
      (∑ b, threeSectorKernel A a b * ip (tripleVacuum b).val f.val) =
        ip (tripleVacuum a).val (A f).val := by
    conv_rhs => rw [← threeSector_frame f]
    simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul,
      inner_sum_right, TwoBodyLift.inner_smul_right, threeSectorKernel, mul_comm]
  simp only [threeBodyLift, tripleCoefficientLift, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, tripleRemove_threeSector,
    map_smul, smul_smul]
  simp_rw [← Finset.sum_smul, hc]
  exact tripleVacuum_parseval (A f)

theorem tripleCoefficientLift_sector (K : Matrix (TripleIndex ι) (TripleIndex ι) ℂ)
    (N : ℕ) (f : Core ι ℂ) (hf : f.IsHomogeneous (N + 3)) :
    (tripleCoefficientLift K f).IsHomogeneous (N + 3) := by
  simp only [tripleCoefficientLift, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro a ha
  apply MvPolynomial.IsHomogeneous.sum
  intro b hb
  rw [MvPolynomial.smul_eq_C_mul]
  exact (tripleCreate_sector a N _ (tripleRemove_sector b N f hf)).C_mul _

def coefficientThreeSector (K : Matrix (TripleIndex ι) (TripleIndex ι) ℂ) :
    ThreeSector ι →ₗ[ℂ] ThreeSector ι :=
  ((tripleCoefficientLift K).comp (ThreeSector ι).subtype).codRestrict _
    (fun f => tripleCoefficientLift_sector K 0 f.val f.property)

theorem tripleCreate_resolution (b : TripleIndex ι) (f : Core ι ℂ) :
    (∑ a, ip (tripleVacuum a).val (tripleVacuum b).val • tripleCreate a f) =
      tripleCreate b f := by
  simp only [tripleCreate_eq_vacuum_mul, ← smul_mul_assoc, ← Finset.sum_mul,
    tripleVacuum_parseval]

theorem ip_ext_right (f g : Core ι ℂ) (h : ∀ p, ip p f = ip p g) : f = g := by
  apply sub_eq_zero.mp
  apply (occupationInner_self_eq_zero_iff (fun _ : ι => 1) (fun _ => by norm_num) (f-g)).mp
  change ip (f-g) (f-g) = 0
  rw [sub_eq_add_neg, ← neg_one_smul ℂ g]
  simp only [ip, occupationInner_add_right, occupationInner_smul_right, neg_one_mul]
  exact sub_eq_zero.mpr (h _)

theorem tripleRemove_resolution (b : TripleIndex ι) (f : Core ι ℂ) :
    (∑ a, ip (tripleVacuum b).val (tripleVacuum a).val • tripleRemove a f) =
      tripleRemove b f := by
  apply ip_ext_right
  intro g
  rw [← tripleRemove_create_adjoint, ← tripleCreate_resolution b g]
  simp only [inner_sum_left, inner_sum_right, TwoBodyLift.inner_smul_left,
    TwoBodyLift.inner_smul_right, tripleRemove_create_adjoint]
  apply Finset.sum_congr rfl
  intro a ha
  rw [show star (ip (tripleVacuum a).val (tripleVacuum b).val) =
    ip (tripleVacuum b).val (tripleVacuum a).val from
    occupationInner_conj_symm (fun _ => 1) _ _]

def threeBodyLiftLinear :
    (ThreeSector ι →ₗ[ℂ] ThreeSector ι) →ₗ[ℂ] (Core ι ℂ →ₗ[ℂ] Core ι ℂ) where
  toFun := threeBodyLift
  map_add' A B := by
    ext f
    simp only [threeBodyLift, tripleCoefficientLift, threeSectorKernel,
      LinearMap.add_apply, Submodule.coe_add, ip, occupationInner_add_right,
      LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
      add_smul, Finset.sum_add_distrib]
  map_smul' c A := by
    ext f
    simp only [threeBodyLift, tripleCoefficientLift, threeSectorKernel,
      LinearMap.smul_apply, Submodule.coe_smul, ip, occupationInner_smul_right,
      LinearMap.sum_apply, LinearMap.comp_apply, smul_smul, Finset.smul_sum]
    rfl

def tripleRankSector (a b : TripleIndex ι) : ThreeSector ι →ₗ[ℂ] ThreeSector ι where
  toFun f := ip (tripleVacuum b).val f.val • tripleVacuum a
  map_add' f g := by
    simp only [Submodule.coe_add, ip, occupationInner_add_right, add_smul]
  map_smul' c f := by
    simp only [Submodule.coe_smul, ip, occupationInner_smul_right, smul_smul]
    rfl

theorem threeBodyLift_rank (a b : TripleIndex ι) :
    threeBodyLift (tripleRankSector a b) = (tripleCreate a).comp (tripleRemove b) := by
  apply LinearMap.ext
  intro f
  have hrow (x : TripleIndex ι) :
      (∑ y, (ip (tripleVacuum b).val (tripleVacuum y).val *
        ip (tripleVacuum x).val (tripleVacuum a).val) •
          tripleCreate x (tripleRemove y f)) =
      ip (tripleVacuum x).val (tripleVacuum a).val •
        tripleCreate x (tripleRemove b f) := by
    rw [← tripleRemove_resolution b f]
    simp only [map_sum, map_smul, Finset.smul_sum, smul_smul, mul_comm]
  simp only [threeBodyLift, tripleCoefficientLift, threeSectorKernel,
    tripleRankSector, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_smul,
    TwoBodyLift.inner_smul_right, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, hrow]
  exact tripleCreate_resolution a _

theorem coefficientThreeSector_expansion (K : Matrix (TripleIndex ι) (TripleIndex ι) ℂ) :
    coefficientThreeSector K = ∑ a, ∑ b, K a b • tripleRankSector a b := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  change tripleCoefficientLift K f.val = _
  simp only [tripleCoefficientLift, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, tripleRemove_threeSector, map_smul, tripleRankSector,
    LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_sum, Submodule.coe_smul]
  rfl

/-- Every normal-ordered three-body polynomial operator is exactly the normalized
lift of its actual three-particle restriction. The assertion is an operator identity
on the full finite core, rather than a supplied comparison at each N. -/
theorem threeBodyLift_restriction (K : Matrix (TripleIndex ι) (TripleIndex ι) ℂ) :
    threeBodyLift (coefficientThreeSector K) = tripleCoefficientLift K := by
  change threeBodyLiftLinear (coefficientThreeSector K) = _
  rw [coefficientThreeSector_expansion]
  simp only [map_sum, map_smul, threeBodyLiftLinear, LinearMap.coe_mk,
    AddHom.coe_mk, threeBodyLift_rank, tripleCoefficientLift]

theorem tripleRemove_low_sector (a : TripleIndex ι) (N : ℕ) (hN : N < 3)
    (f : Core ι ℂ) (hf : f.IsHomogeneous N) : tripleRemove a f = 0 := by
  simp only [tripleRemove, LinearMap.smul_apply, LinearMap.comp_apply]
  rcases N with _ | _ | _ | N
  · rw [annihilate_homogeneous_zero a.1 f hf, map_zero, map_zero, smul_zero]
  · have h1 := TorusLean.BosonBridge.OccupationInstance.annihilate_sector 0 a.1 f hf
    rw [annihilate_homogeneous_zero a.2.1 _ h1, map_zero, smul_zero]
  · have h1 := TorusLean.BosonBridge.OccupationInstance.annihilate_sector 1 a.1 f hf
    have h2 := TorusLean.BosonBridge.OccupationInstance.annihilate_sector 0 a.2.1 _ h1
    rw [annihilate_homogeneous_zero a.2.2 _ h2, smul_zero]
  · omega

theorem tripleCoefficientLift_low_sector (K : Matrix (TripleIndex ι) (TripleIndex ι) ℂ)
    (N : ℕ) (hN : N < 3) (f : Core ι ℂ) (hf : f.IsHomogeneous N) :
    tripleCoefficientLift K f = 0 := by
  simp only [tripleCoefficientLift, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, tripleRemove_low_sector _ N hN f hf,
    map_zero, smul_zero, Finset.sum_const_zero]

theorem tripleCoefficientLift_sector_all (K : Matrix (TripleIndex ι) (TripleIndex ι) ℂ)
    (N : ℕ) (f : Core ι ℂ) (hf : f.IsHomogeneous N) :
    (tripleCoefficientLift K f).IsHomogeneous N := by
  by_cases hN : N < 3
  · rw [tripleCoefficientLift_low_sector K N hN f hf]
    exact MvPolynomial.isHomogeneous_zero (σ := ι) (R := ℂ) N
  · obtain ⟨n, rfl⟩ : ∃ n, N = n + 3 := ⟨N-3, by omega⟩
    exact tripleCoefficientLift_sector K n f hf

def sectorThreeBodyLift (A : ThreeSector ι →ₗ[ℂ] ThreeSector ι) (N : ℕ) :
    MvPolynomial.homogeneousSubmodule ι ℂ N →ₗ[ℂ]
      MvPolynomial.homogeneousSubmodule ι ℂ N :=
  ((threeBodyLift A).comp (MvPolynomial.homogeneousSubmodule ι ℂ N).subtype).codRestrict _
    (fun f => tripleCoefficientLift_sector_all (threeSectorKernel A) N f.val f.property)

#print axioms tripleCreate_remove_adjoint
#print axioms tripleRemove_create_adjoint
#print axioms tripleRemove_sector
#print axioms tripleCreate_sector
#print axioms tripleCreate_eq_vacuum_mul
#print axioms tripleRemove_threeSector
#print axioms tripleRemove_support_subset
#print axioms tripleCoefficientLift_inner
#print axioms tripleCoefficientLift_inner_coefficients
#print axioms tripleCoefficientLift_nonneg
#print axioms euler_one
#print axioms euler_three
#print axioms tripleResolution
#print axioms tripleVacuum_parseval
#print axioms threeSectorKernel_form
#print axioms threeSectorKernel_posSemidef
#print axioms threeBodyLift_nonneg
#print axioms threeSectorKernel_sub
#print axioms tripleCoefficientLift_sub
#print axioms threeBodyLift_sub
#print axioms threeBodyLift_mono
#print axioms threeSector_frame
#print axioms threeBodyLift_threeSector
#print axioms tripleCoefficientLift_sector
#print axioms tripleCreate_resolution
#print axioms ip_ext_right
#print axioms tripleRemove_resolution
#print axioms threeBodyLift_rank
#print axioms coefficientThreeSector_expansion
#print axioms threeBodyLift_restriction
#print axioms tripleRemove_low_sector
#print axioms tripleCoefficientLift_low_sector
#print axioms tripleCoefficientLift_sector_all

end TorusLean.Shared.BosonThreeBodyLift
