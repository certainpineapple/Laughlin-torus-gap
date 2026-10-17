import torus.shared.LLLTensorReconstruction
import Mathlib.Analysis.Calculus.FDeriv.Pi

set_option autoImplicit false
noncomputable section

namespace TorusLean.Shared.PhysicalNBodyCarrier

open TorusLean.Geometry TorusLean.Shared.LLLSliceReconstruction
open TorusLean.Shared.LLLTensorReconstruction

/-- Original product Gaussian, before any basis or tensor representation. -/
def configurationGaussian (N : ℕ) (z : Fin N → ℂ) : ℂ :=
  ∏ a, gaussianFactor 1 (z a)

/-- A jointly entire factor on the full complex configuration space. -/
def JointGaussianHolomorphic (N : ℕ) (f : (Fin N → ℂ) → ℂ) : Prop :=
  ∃ H : (Fin N → ℂ) → ℂ, Differentiable ℂ H ∧
    ∀ z, f z = configurationGaussian N z * H z

/-- The original single-particle magnetic law in each coordinate at all
spectator points, not a statement about expansion coefficients. -/
def ParticleBoundary (G : Geometry) (theta : Twist) (N : ℕ)
    (f : (Fin N → ℂ) → ℂ) : Prop :=
  ∀ a : Fin N, ∀ z : Fin N → ℂ,
    HasLatticeBoundary G.M 1 G.omega1 G.omega2 theta.theta1 theta.theta2
      (fun t => f (Function.update z a t))

def BosonSymmetric (N : ℕ) (f : (Fin N → ℂ) → ℂ) : Prop :=
  ∀ σ : Equiv.Perm (Fin N), ∀ z, f (z ∘ σ) = f z

/-- Independently defined full pointwise physical boson carrier. No image,
integrability, dimension, or completeness assumption is built into it. -/
def PhysicalBosonCarrier (G : Geometry) (theta : Twist) (N : ℕ) :=
  {f : (Fin N → ℂ) → ℂ // JointGaussianHolomorphic N f ∧
    ParticleBoundary G theta N f ∧ BosonSymmetric N f}

theorem configurationGaussian_update (N : ℕ) (z : Fin N → ℂ) (a : Fin N) (t : ℂ) :
    configurationGaussian N (Function.update z a t) =
      gaussianFactor 1 t * ∏ b ∈ Finset.univ \ {a}, gaussianFactor 1 (z b) := by
  classical
  have hfun : (fun b => gaussianFactor 1 (Function.update z a t b)) =
      Function.update (fun b => gaussianFactor 1 (z b)) a (gaussianFactor 1 t) := by
    funext b
    by_cases h : b = a <;> simp [h]
  unfold configurationGaussian
  rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ a)]

theorem joint_and_boundary_has_slices (G : Geometry) (theta : Twist) (N : ℕ)
    (f : (Fin N → ℂ) → ℂ) (hj : JointGaussianHolomorphic N f)
    (hb : ParticleBoundary G theta N f) : HasLLLSlices G theta N f := by
  classical
  obtain ⟨H, hH, hfactor⟩ := hj
  intro a z
  refine ⟨⟨fun t => f (Function.update z a t), ?_⟩, fun _ => rfl⟩
  unfold rawLLLSubmodule
  change IsGaussianHolomorphic ((1 : ℕ) : ℝ) (fun t => f (Function.update z a t)) ∧ _
  simp only [Nat.cast_one]
  refine ⟨?_, hb a z⟩
  refine ⟨fun t => (∏ b ∈ Finset.univ \ {a}, gaussianFactor 1 (z b)) *
    H (Function.update z a t), ?_, ?_⟩
  · exact (hH.comp (fun t => (hasFDerivAt_update (𝕜 := ℂ) z t).differentiableAt)).const_mul _
  · intro t
    dsimp only
    rw [hfactor, configurationGaussian_update]
    ring

/-- Finite products of jointly entire scalar factors stay jointly entire. -/
theorem differentiable_configuration_product {N : ℕ} {I : Type*}
    (H : I → ℂ → ℂ) (hH : ∀ i, Differentiable ℂ (H i)) (w : Fin N → I) :
    Differentiable ℂ (fun z : Fin N → ℂ => ∏ a, H (w a) (z a)) := by
  classical
  have h (s : Finset (Fin N)) :
      Differentiable ℂ (fun z : Fin N → ℂ => ∏ a ∈ s, H (w a) (z a)) := by
    induction s using Finset.induction_on with
    | empty => simpa using (differentiable_const (1 : ℂ) :
        Differentiable ℂ (fun _ : Fin N → ℂ => (1 : ℂ)))
    | @insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact ((hH (w a)).comp (differentiable_apply a)).mul ih
  exact h Finset.univ

/-- Slice membership implies joint entire Gaussian factor by actual finite
tensor reconstruction. The finite basis is derived, not a physical premise. -/
theorem slices_joint_gaussian (G : Geometry) (theta : Twist) (N : ℕ)
    (f : (Fin N → ℂ) → ℂ) (hf : HasLLLSlices G theta N f) :
    JointGaussianHolomorphic N f := by
  classical
  let b := Module.finBasis ℂ (LLL G theta 1)
  have hb : ∀ i, ∃ H : ℂ → ℂ, Differentiable ℂ H ∧
      ∀ t, (b i).val t = gaussianFactor 1 t * H t := by
    intro i
    simpa only [IsGaussianHolomorphic, Nat.cast_one] using (b i).property.1
  choose H hH hfactor using hb
  obtain ⟨c, hc⟩ := slices_tensor_expansion G theta b N f hf
  refine ⟨fun z => ∑ w, c w * ∏ a, H (w a) (z a), ?_, ?_⟩
  · apply Differentiable.fun_sum
    intro w _
    exact (differentiable_configuration_product H hH w).const_mul (c w)
  · intro z
    rw [hc]
    simp_rw [hfactor, Finset.prod_mul_distrib]
    unfold configurationGaussian
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring

theorem slices_particle_boundary (G : Geometry) (theta : Twist) (N : ℕ)
    (f : (Fin N → ℂ) → ℂ) (hf : HasLLLSlices G theta N f) :
    ParticleBoundary G theta N f := by
  intro a z
  obtain ⟨h, hh⟩ := hf a z
  have heq : h.val = (fun t => f (Function.update z a t)) := funext hh
  rw [← heq]
  exact h.property.2

/-- Pointwise equivalence to the independent full physical predicate. -/
theorem slices_iff_joint_and_boundary (G : Geometry) (theta : Twist) (N : ℕ)
    (f : (Fin N → ℂ) → ℂ) : HasLLLSlices G theta N f ↔
      JointGaussianHolomorphic N f ∧ ParticleBoundary G theta N f := by
  constructor
  · intro hf
    exact ⟨slices_joint_gaussian G theta N f hf, slices_particle_boundary G theta N f hf⟩
  · rintro ⟨hj,hb⟩
    exact joint_and_boundary_has_slices G theta N f hj hb

#print axioms configurationGaussian_update
#print axioms joint_and_boundary_has_slices
#print axioms differentiable_configuration_product
#print axioms slices_joint_gaussian
#print axioms slices_particle_boundary
#print axioms slices_iff_joint_and_boundary

end TorusLean.Shared.PhysicalNBodyCarrier
