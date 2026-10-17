import OccupationInstance
import torus.boson.PolynomialInnerAdjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Normalize

/-!
Actual unitary change of modes on the shared finite polynomial core.
The one-particle space here is EuclideanSpace ℂ ι. Its identification with
the physical torus LLL, including the raw coherent-vector norm, is pending.
-/

set_option autoImplicit false

namespace TorusLean.Boson.UnitaryTransport

open scoped BigOperators ComplexConjugate
open TorusLean.Boson

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable section

abbrev Orbital (ι : Type*) [Fintype ι] := EuclideanSpace ℂ ι
abbrev Unitary (ι : Type*) [Fintype ι] := Orbital ι ≃ₗᵢ[ℂ] Orbital ι

def modeCreate (β : Orbital ι) : Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  ∑ i, β i • create i

def modeAnnihilate (β : Orbital ι) : Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  ∑ i, star (β i) • annihilate i

def modePair (β : Orbital ι) : Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  ((Real.sqrt 2)⁻¹ : ℂ) • (modeAnnihilate β).comp (modeAnnihilate β)

def modeLinear (β : Orbital ι) : Core ι ℂ :=
  ∑ i, MvPolynomial.C (β i) * MvPolynomial.X i

def secondQuantization (U : Unitary ι) : Core ι ℂ →ₐ[ℂ] Core ι ℂ :=
  MvPolynomial.aeval (fun i => modeLinear (U (EuclideanSpace.single i 1)))

theorem modeCreate_apply (β : Orbital ι) (f : Core ι ℂ) :
    modeCreate β f = modeLinear β * f := by
  simp [modeCreate, modeLinear, create, Finset.sum_mul, MvPolynomial.smul_eq_C_mul,
    mul_assoc]

theorem modeCreate_single (i : ι) :
    modeCreate (EuclideanSpace.single i 1) = create i := by
  simp [modeCreate, PiLp.single_apply]

theorem modeAnnihilate_single (i : ι) :
    modeAnnihilate (EuclideanSpace.single i 1) = annihilate i := by
  simp [modeAnnihilate, PiLp.single_apply, apply_ite star]

theorem modePair_single (i : ι) (f : Core ι ℂ) :
    modePair (EuclideanSpace.single i 1) f = TorusLean.BosonBridge.OccupationInstance.normalizedUnitPair i f := by
  simp [modePair, modeAnnihilate_single, TorusLean.BosonBridge.OccupationInstance.normalizedUnitPair, pairAnnihilate]

theorem canonical_inner_sum_left (s : Finset ι) (f : ι → Core ι ℂ) (g : Core ι ℂ) :
    occupationInner (fun _ => 1) (∑ i ∈ s, f i) g =
      ∑ i ∈ s, occupationInner (fun _ => 1) (f i) g := by
  induction s using Finset.induction_on with
  | empty => simp [occupationInner_zero_left]
  | @insert i s hi ih => simp [hi, occupationInner_add_left, ih]

theorem canonical_inner_sum_right (s : Finset ι) (f : Core ι ℂ) (g : ι → Core ι ℂ) :
    occupationInner (fun _ => 1) f (∑ i ∈ s, g i) =
      ∑ i ∈ s, occupationInner (fun _ => 1) f (g i) := by
  induction s using Finset.induction_on with
  | empty => simp [occupationInner_zero_right]
  | @insert i s hi ih => simp [hi, occupationInner_add_right, ih]

theorem mode_create_adjoint (β : Orbital ι) (f g : Core ι ℂ) :
    occupationInner (fun _ => 1) (modeCreate β f) g =
      occupationInner (fun _ => 1) f (modeAnnihilate β g) := by
  simp only [modeCreate, modeAnnihilate, LinearMap.sum_apply, LinearMap.smul_apply]
  rw [canonical_inner_sum_left, canonical_inner_sum_right]
  simp only [occupationInner_smul_left, occupationInner_smul_right,
    create_adjoint_canonical]

theorem mode_mixed_ccr (β γ : Orbital ι) (f : Core ι ℂ) :
    modeAnnihilate β (modeCreate γ f) =
      modeCreate γ (modeAnnihilate β f) + (inner ℂ β γ) • f := by
  simp only [modeAnnihilate, modeCreate, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, annihilate_create, smul_add, Finset.sum_add_distrib]
  simp only [Finset.smul_sum]
  apply congrArg₂ (· + ·)
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    exact smul_comm _ _ _
  · simp [smul_ite, PiLp.inner_apply, RCLike.inner_apply, Finset.sum_smul,
      ← smul_smul, mul_comm]

theorem secondQuantization_C (U : Unitary ι) (c : ℂ) :
    secondQuantization U (MvPolynomial.C c) = MvPolynomial.C c := by
  simp [secondQuantization]

theorem secondQuantization_create (U : Unitary ι) (i : ι) (f : Core ι ℂ) :
    secondQuantization U (create i f) =
      modeCreate (U (EuclideanSpace.single i 1)) (secondQuantization U f) := by
  simp [secondQuantization, create, modeCreate_apply]

theorem unitary_column_inner (U : Unitary ι) (i j : ι) :
    inner ℂ (U (EuclideanSpace.single i 1)) (U (EuclideanSpace.single j 1)) =
      if i = j then 1 else 0 := by
  rw [U.inner_map_map]
  simp [EuclideanSpace.inner_single_left, PiLp.single_apply]

theorem modeAnnihilate_C (β : Orbital ι) (c : ℂ) :
    modeAnnihilate β (MvPolynomial.C c) = 0 := by
  simp [modeAnnihilate, annihilate]

theorem secondQuantization_annihilate (U : Unitary ι) (i : ι) (f : Core ι ℂ) :
    modeAnnihilate (U (EuclideanSpace.single i 1)) (secondQuantization U f) =
      secondQuantization U (annihilate i f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [secondQuantization_C, modeAnnihilate_C, annihilate]
  | add f g hf hg => simp [map_add, hf, hg]
  | mul_X f j hf =>
    have hc : f * MvPolynomial.X j = create j f := by simp [create, mul_comm]
    rw [hc, secondQuantization_create, mode_mixed_ccr, hf,
      annihilate_create, map_add, secondQuantization_create, unitary_column_inner]
    by_cases h : i = j <;> simp [h]

theorem secondQuantization_constantCoeff (U : Unitary ι) (f : Core ι ℂ) :
    MvPolynomial.constantCoeff (secondQuantization U f) =
      MvPolynomial.constantCoeff f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [secondQuantization_C]
  | add f g hf hg => simp [map_add, hf, hg]
  | mul_X f j hf =>
    simp [secondQuantization, modeLinear, map_sum, map_mul]

theorem canonical_inner_C_left (c : ℂ) (g : Core ι ℂ) :
    occupationInner (fun _ => 1) (MvPolynomial.C c) g =
      star c * MvPolynomial.constantCoeff g := by
  change occupationInner (fun _ => 1) (MvPolynomial.monomial 0 c) g = _
  rw [occupationInner_monomial_left]
  simp [occupationMetricWeight, MvPolynomial.constantCoeff]

/-- Isometry is a proved identity for this actual polynomial substitution. -/
theorem secondQuantization_inner (U : Unitary ι) (f g : Core ι ℂ) :
    occupationInner (fun _ => 1) (secondQuantization U f) (secondQuantization U g) =
      occupationInner (fun _ => 1) f g := by
  induction f using MvPolynomial.induction_on generalizing g with
  | C c =>
    rw [secondQuantization_C, canonical_inner_C_left, canonical_inner_C_left,
      secondQuantization_constantCoeff]
  | add f h hf hh =>
    simp only [map_add, occupationInner_add_left, hf, hh]
  | mul_X f i hf =>
    have hc : f * MvPolynomial.X i = create i f := by simp [create, mul_comm]
    rw [hc, secondQuantization_create, mode_create_adjoint,
      secondQuantization_annihilate, hf, create_adjoint_canonical]

theorem secondQuantization_normSq (U : Unitary ι) (f : Core ι ℂ) :
    occupationMetricNormSq (fun _ => 1) (secondQuantization U f) =
      occupationMetricNormSq (fun _ => 1) f := by
  simpa only [occupationInner_self_re] using
    congrArg Complex.re (secondQuantization_inner U f f)

theorem orbital_expansion (β : Orbital ι) :
    ∑ i, β i • EuclideanSpace.single i 1 = β := by
  ext i
  simp [Pi.single_apply]

theorem modeLinear_add (β γ : Orbital ι) :
    modeLinear (β + γ) = modeLinear β + modeLinear γ := by
  simp [modeLinear, PiLp.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem modeLinear_smul (c : ℂ) (β : Orbital ι) :
    modeLinear (c • β) = c • modeLinear β := by
  simp [modeLinear, PiLp.smul_apply, smul_eq_mul, map_mul, mul_assoc,
    MvPolynomial.smul_eq_C_mul, Finset.mul_sum]

def modeLinearMap : Orbital ι →ₗ[ℂ] Core ι ℂ where
  toFun := modeLinear
  map_add' := modeLinear_add
  map_smul' := modeLinear_smul

theorem secondQuantization_modeLinear (U : Unitary ι) (β : Orbital ι) :
    secondQuantization U (modeLinear β) = modeLinear (U β) := by
  have hu : U β = ∑ i, β i • U (EuclideanSpace.single i 1) := by
    nth_rw 1 [← orbital_expansion β]
    simp only [map_sum, map_smul]
  rw [hu]
  change _ = modeLinearMap (∑ i, β i • U (EuclideanSpace.single i 1))
  simp only [map_sum, map_smul]
  simp [secondQuantization, modeLinear, modeLinearMap, MvPolynomial.smul_eq_C_mul]

theorem secondQuantization_trans (U V : Unitary ι) (f : Core ι ℂ) :
    secondQuantization U (secondQuantization V f) =
      secondQuantization (V.trans U) f := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [secondQuantization_C]
  | add f g hf hg => simp [map_add, hf, hg]
  | mul_X f i hf =>
    simp only [map_mul, secondQuantization, MvPolynomial.aeval_X]
    change secondQuantization U (secondQuantization V f) *
      secondQuantization U (modeLinear (V (EuclideanSpace.single i 1))) = _
    rw [hf, secondQuantization_modeLinear]
    rfl

theorem secondQuantization_refl (f : Core ι ℂ) :
    secondQuantization (LinearIsometryEquiv.refl ℂ (Orbital ι)) f = f := by
  have hx : (fun i : ι => modeLinear (EuclideanSpace.single i 1)) = MvPolynomial.X := by
    funext i
    simp [modeLinear, PiLp.single_apply]
  simpa [secondQuantization, hx] using MvPolynomial.aeval_X_left_apply f

theorem secondQuantization_inverse (U : Unitary ι) (f : Core ι ℂ) :
    secondQuantization U (secondQuantization U.symm f) = f := by
  rw [secondQuantization_trans]
  simpa using secondQuantization_refl f

theorem secondQuantization_pair (U : Unitary ι) (i : ι) (f : Core ι ℂ) :
    modePair (U (EuclideanSpace.single i 1)) (secondQuantization U f) =
      secondQuantization U (TorusLean.BosonBridge.OccupationInstance.normalizedUnitPair i f) := by
  simp only [modePair, LinearMap.smul_apply, LinearMap.comp_apply,
    secondQuantization_annihilate,
    TorusLean.BosonBridge.OccupationInstance.normalizedUnitPair, map_smul,
    pairAnnihilate, LinearMap.comp_apply]

/-- The target estimate is transported from the proved coordinate estimate;
no isometry, covariance, or occupation estimate is an input hypothesis. -/
theorem unitary_column_occupation_control (U : Unitary ι) (i : ι) (f : Core ι ℂ) :
    occupationMetricNormSq (fun _ => 1) (modeAnnihilate (U (EuclideanSpace.single i 1)) f) ≤
      occupationMetricNormSq (fun _ => 1) (modePair (U (EuclideanSpace.single i 1)) f) +
        occupationMetricNormSq (fun _ => 1) f := by
  let g := secondQuantization U.symm f
  have hf : secondQuantization U g = f := secondQuantization_inverse U f
  have h := TorusLean.BosonBridge.OccupationInstance.unit_mode_occupation_control
    (fun _ : ι => 1) i rfl g
  rw [← secondQuantization_normSq U (annihilate i g),
    ← secondQuantization_normSq U
      (TorusLean.BosonBridge.OccupationInstance.normalizedUnitPair i g),
    ← secondQuantization_normSq U g] at h
  rw [← secondQuantization_annihilate, ← secondQuantization_pair, hf] at h
  exact h

theorem exists_unitary_maps_single (i : ι) (β : Orbital ι) (hβ : ‖β‖ = 1) :
    ∃ U : Unitary ι, U (EuclideanSpace.single i 1) = β := by
  have hon : Orthonormal ℂ
      (({i} : Set ι).domRestrict (fun _ : ι => β)) := by
    apply orthonormal_subsingleton_iff.mpr
    intro j
    exact hβ
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  exact ⟨b.repr.symm, (b.repr_symm_single i).trans (hb i (by simp))⟩

theorem normalized_mode_occupation_control [Nonempty ι]
    (β : Orbital ι) (hβ : ‖β‖ = 1) (f : Core ι ℂ) :
    occupationMetricNormSq (fun _ => 1) (modeAnnihilate β f) ≤
      occupationMetricNormSq (fun _ => 1) (modePair β f) +
        occupationMetricNormSq (fun _ => 1) f := by
  obtain ⟨U, hU⟩ := exists_unitary_maps_single (Classical.arbitrary ι) β hβ
  simpa only [hU] using unitary_column_occupation_control U (Classical.arbitrary ι) f

theorem normalized_mode_pair_output_control [Nonempty ι]
    (β : Orbital ι) (hβ : ‖β‖ = 1) (f : Core ι ℂ) :
    occupationMetricNormSq (fun _ => 1) (modeAnnihilate β (modePair β f)) ≤
      occupationMetricNormSq (fun _ => 1) (modePair β (modePair β f)) +
        occupationMetricNormSq (fun _ => 1) (modePair β f) :=
  normalized_mode_occupation_control β hβ (modePair β f)

theorem modeAnnihilate_smul (c : ℂ) (β : Orbital ι) :
    modeAnnihilate (c • β) = star c • modeAnnihilate β := by
  ext f
  simp [modeAnnihilate, PiLp.smul_apply, star_mul, Finset.smul_sum, smul_smul, mul_comm]

theorem modePair_smul (c : ℂ) (β : Orbital ι) (f : Core ι ℂ) :
    modePair (c • β) f = (star c) ^ 2 • modePair β f := by
  simp only [modePair, modeAnnihilate_smul, LinearMap.smul_apply,
    LinearMap.comp_apply, map_smul, smul_smul]
  congr 1
  ring

theorem raw_annihilation_normSq [Nonempty ι] (c : ℂ) (β : Orbital ι) (f : Core ι ℂ) :
    occupationMetricNormSq (fun _ => 1) (modeAnnihilate (c • β) f) =
      Complex.normSq c * occupationMetricNormSq (fun _ => 1) (modeAnnihilate β f) := by
  rw [modeAnnihilate_smul, LinearMap.smul_apply,
    TorusLean.BosonBridge.OccupationInstance.metricNormSq_smul (fun _ => 1)
      _ _ (Classical.arbitrary ι)]
  simp [Complex.star_def]

theorem raw_pair_normSq [Nonempty ι] (c : ℂ) (β : Orbital ι) (f : Core ι ℂ) :
    occupationMetricNormSq (fun _ => 1) (modePair (c • β) f) =
      (Complex.normSq c) ^ 2 * occupationMetricNormSq (fun _ => 1) (modePair β f) := by
  rw [modePair_smul,
    TorusLean.BosonBridge.OccupationInstance.metricNormSq_smul (fun _ => 1)
      _ _ (Classical.arbitrary ι)]
  simp [pow_two, Complex.normSq_mul, Complex.star_def]

/-- Exact raw-vector factors: if u = sqrt(k) β, single removal has factor k
and the pair norm squared has factor k². k is an explicit nonnegative input. -/
theorem sqrt_raw_mode_factors [Nonempty ι] (k : ℝ) (hk : 0 ≤ k)
    (β : Orbital ι) (f : Core ι ℂ) :
    occupationMetricNormSq (fun _ => 1) (modeAnnihilate ((Real.sqrt k : ℂ) • β) f) =
        k * occupationMetricNormSq (fun _ => 1) (modeAnnihilate β f) ∧
      occupationMetricNormSq (fun _ => 1) (modePair ((Real.sqrt k : ℂ) • β) f) =
        k ^ 2 * occupationMetricNormSq (fun _ => 1) (modePair β f) := by
  rw [raw_annihilation_normSq, raw_pair_normSq, Complex.normSq_ofReal,
    Real.mul_self_sqrt hk]
  exact ⟨rfl, rfl⟩

/-- B(u)=k B(β) for u=sqrt(k) β, retaining the normalized-pair 1/sqrt(2). -/
theorem sqrt_raw_pair [Nonempty ι] (k : ℝ) (hk : 0 ≤ k) (β : Orbital ι) (f : Core ι ℂ) :
    modePair ((Real.sqrt k : ℂ) • β) f = (k : ℂ) • modePair β f := by
  rw [modePair_smul]
  have hs : star (Real.sqrt k : ℂ) ^ 2 = (k : ℂ) := by
    simp only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_pow]
    rw [Real.sq_sqrt hk]
  rw [hs]

theorem sqrt_raw_occupation_control [Nonempty ι] (k : ℝ) (hk : 0 ≤ k)
    (β : Orbital ι) (hβ : ‖β‖ = 1) (f : Core ι ℂ) :
    occupationMetricNormSq (fun _ => 1) (modeAnnihilate ((Real.sqrt k : ℂ) • β) f) ≤
      k * occupationMetricNormSq (fun _ => 1) (modePair β f) +
        k * occupationMetricNormSq (fun _ => 1) f := by
  rw [(sqrt_raw_mode_factors k hk β f).1]
  have h := mul_le_mul_of_nonneg_left (normalized_mode_occupation_control β hβ f) hk
  simpa only [mul_add] using h

theorem modeLinear_sector (β : Orbital ι) : (modeLinear β).IsHomogeneous 1 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  exact MvPolynomial.isHomogeneous_C_mul_X (β i) i

theorem secondQuantization_sector (U : Unitary ι) (N : ℕ) (f : Core ι ℂ)
    (hf : f.IsHomogeneous N) : (secondQuantization U f).IsHomogeneous N := by
  simpa only [secondQuantization, one_mul] using
    hf.aeval (fun i => modeLinear (U (EuclideanSpace.single i 1)))
      (fun i => modeLinear_sector _)

theorem modeAnnihilate_sector (β : Orbital ι) (N : ℕ) (f : Core ι ℂ)
    (hf : f.IsHomogeneous (N + 1)) : (modeAnnihilate β f).IsHomogeneous N := by
  simp only [modeAnnihilate, LinearMap.sum_apply, LinearMap.smul_apply]
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  rw [MvPolynomial.smul_eq_C_mul]
  exact (TorusLean.BosonBridge.OccupationInstance.annihilate_sector N i f hf).C_mul _

theorem modePair_sector (β : Orbital ι) (N : ℕ) (f : Core ι ℂ)
    (hf : f.IsHomogeneous (N + 2)) : (modePair β f).IsHomogeneous N := by
  have h1 : (modeAnnihilate β f).IsHomogeneous (N + 1) :=
    modeAnnihilate_sector β (N + 1) f (by simpa only [Nat.add_assoc] using hf)
  have h2 := modeAnnihilate_sector β N (modeAnnihilate β f) h1
  simp only [modePair, LinearMap.smul_apply, LinearMap.comp_apply,
    MvPolynomial.smul_eq_C_mul]
  exact h2.C_mul _

/-- Four removals and the intervening spectator are genuine maps between
the indicated homogeneous sectors, with a uniform constant one bound. -/
theorem normalized_mode_four_body_control [Nonempty ι]
    (β : Orbital ι) (hβ : ‖β‖ = 1) (N : ℕ) (f : Core ι ℂ)
    (hf : f.IsHomogeneous (N + 4)) :
    (modePair β f).IsHomogeneous (N + 2) ∧
      (modeAnnihilate β (modePair β f)).IsHomogeneous (N + 1) ∧
      (modePair β (modePair β f)).IsHomogeneous N ∧
      occupationMetricNormSq (fun _ => 1) (modeAnnihilate β (modePair β f)) ≤
        occupationMetricNormSq (fun _ => 1) (modePair β (modePair β f)) +
          occupationMetricNormSq (fun _ => 1) (modePair β f) := by
  have hp : (modePair β f).IsHomogeneous (N + 2) :=
    modePair_sector β (N + 2) f (by simpa only [Nat.add_assoc] using hf)
  refine ⟨hp, ?_, modePair_sector β N _ hp,
    normalized_mode_pair_output_control β hβ f⟩
  exact modeAnnihilate_sector β (N + 1) _ (by simpa only [Nat.add_assoc] using hp)

theorem raw_vector_expansion (u : Orbital ι) :
    (‖u‖ : ℂ) • NormedSpace.normalize u = u := by
  ext i
  have h := congrArg (fun v : Orbital ι => v i) (NormedSpace.norm_smul_normalize u)
  simpa only [PiLp.smul_apply, smul_eq_mul, Complex.real_smul] using! h

/-- Uses the actual Euclidean norm of u, rather than postulating a unit raw
mode. The zero vector is included in both exact factor identities. -/
theorem raw_vector_factors [Nonempty ι] (u : Orbital ι) (f : Core ι ℂ) :
    occupationMetricNormSq (fun _ => 1) (modeAnnihilate u f) =
        ‖u‖ ^ 2 * occupationMetricNormSq (fun _ => 1)
          (modeAnnihilate (NormedSpace.normalize u) f) ∧
      occupationMetricNormSq (fun _ => 1) (modePair u f) =
        ‖u‖ ^ 4 * occupationMetricNormSq (fun _ => 1)
          (modePair (NormedSpace.normalize u) f) := by
  have ha := raw_annihilation_normSq (‖u‖ : ℂ) (NormedSpace.normalize u) f
  have hp := raw_pair_normSq (‖u‖ : ℂ) (NormedSpace.normalize u) f
  rw [raw_vector_expansion] at ha hp
  constructor
  · simpa only [Complex.normSq_ofReal, pow_two] using ha
  · convert hp using 1 <;> simp only [Complex.normSq_ofReal] <;> ring

theorem raw_vector_pair [Nonempty ι] (u : Orbital ι) (f : Core ι ℂ) :
    modePair u f = ((‖u‖ ^ 2 : ℝ) : ℂ) • modePair (NormedSpace.normalize u) f := by
  have hp := modePair_smul (‖u‖ : ℂ) (NormedSpace.normalize u) f
  rw [raw_vector_expansion] at hp
  simpa only [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_pow] using hp

theorem raw_vector_occupation_control [Nonempty ι]
    (u : Orbital ι) (hu : u ≠ 0) (f : Core ι ℂ) :
    occupationMetricNormSq (fun _ => 1) (modeAnnihilate u f) ≤
      ‖u‖ ^ 2 * occupationMetricNormSq (fun _ => 1)
        (modePair (NormedSpace.normalize u) f) +
      ‖u‖ ^ 2 * occupationMetricNormSq (fun _ => 1) f := by
  rw [(raw_vector_factors u f).1]
  have h := mul_le_mul_of_nonneg_left
    (normalized_mode_occupation_control (NormedSpace.normalize u)
      (NormedSpace.norm_normalize hu) f) (sq_nonneg ‖u‖)
  simpa only [mul_add] using h

end
end TorusLean.Boson.UnitaryTransport
