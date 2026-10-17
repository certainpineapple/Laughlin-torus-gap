import torus.shared.PhysicalBosonSurjectivity

set_option autoImplicit false
noncomputable section

namespace TorusLean.Shared.PhysicalBosonMembership

open MeasureTheory
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.LLLSliceReconstruction TorusLean.Shared.PhysicalBosonSurjectivity

/-- All-point slices form an actual function submodule. -/
def sliceSubmodule (G : Geometry) (theta : Twist) (N : ℕ) :
    Submodule ℂ ((Fin N → ℂ) → ℂ) where
  carrier := {f | HasLLLSlices G theta N f}
  zero_mem' := by
    intro a z
    exact ⟨0, fun _ => rfl⟩
  add_mem' := by
    intro f g hf hg a z
    obtain ⟨u,hu⟩ := hf a z
    obtain ⟨v,hv⟩ := hg a z
    exact ⟨u+v, fun t => congrArg₂ (·+·) (hu t) (hv t)⟩
  smul_mem' := by
    intro c f hf a z
    obtain ⟨u,hu⟩ := hf a z
    exact ⟨c • u, fun t => congrArg (fun q : ℂ => c*q) (hu t)⟩

theorem product_sections_has_slices (G : Geometry) (theta : Twist) (N : ℕ)
    (u : Fin N → LLL G theta 1) :
    HasLLLSlices G theta N (fun z => ∏ a, (u a).val (z a)) := by
  classical
  intro a z
  let C := ∏ b ∈ Finset.univ \ {a}, (u b).val (z b)
  refine ⟨C • u a, ?_⟩
  intro t
  have hfun : (fun b => (u b).val (Function.update z a t b)) =
      Function.update (fun b => (u b).val (z b)) a ((u a).val t) := by
    funext b
    by_cases h : b = a <;> simp [h]
  change C * (u a).val t = ∏ b, (u b).val (Function.update z a t b)
  rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ a)]
  exact mul_comm _ _

theorem wordFunction_has_slices (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta N) : HasLLLSlices G theta N (wordFunction G theta N w) :=
  product_sections_has_slices G theta N (fun a => orbitalBasis G theta (w a))

theorem symWordFunction_has_slices (G : Geometry) (theta : Twist) (N : ℕ)
    (w : Word G theta N) : HasLLLSlices G theta N (symWordFunction G theta N w) := by
  classical
  change (fun z => (((Real.sqrt (N.factorial : ℝ))⁻¹ : ℝ) : ℂ) *
    ∑ σ : Equiv.Perm (Fin N), wordFunction G theta N (w ∘ σ) z) ∈ sliceSubmodule G theta N
  have h : (∑ σ : Equiv.Perm (Fin N), wordFunction G theta N (w ∘ σ)) ∈
      sliceSubmodule G theta N :=
    (sliceSubmodule G theta N).sum_mem (fun σ _ => wordFunction_has_slices G theta N _)
  have heq : (fun z => (((Real.sqrt (N.factorial : ℝ))⁻¹ : ℝ) : ℂ) *
      ∑ σ : Equiv.Perm (Fin N), wordFunction G theta N (w ∘ σ) z) =
      ((((Real.sqrt (N.factorial : ℝ))⁻¹ : ℝ) : ℂ)) •
        (∑ σ : Equiv.Perm (Fin N), wordFunction G theta N (w ∘ σ)) := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  rw [heq]
  exact (sliceSubmodule G theta N).smul_mem _ h

theorem occupationFunction_has_slices (G : Geometry) (theta : Twist) (N : ℕ)
    (n : OrbitalIndex G theta →₀ ℕ) :
    HasLLLSlices G theta N (occupationFunction G theta N n) := by
  classical
  unfold occupationFunction
  split_ifs with hn
  · exact symWordFunction_has_slices G theta N _
  · exact (sliceSubmodule G theta N).zero_mem

theorem coreFunction_has_slices (G : Geometry) (theta : Twist) (N : ℕ)
    (p : TorusLean.Boson.Core (OrbitalIndex G theta) ℂ) :
    HasLLLSlices G theta N (coreFunction G theta N p) := by
  classical
  have heq : coreFunction G theta N p =
      ∑ n ∈ p.support, p.coeff n • occupationFunction G theta N n := by
    funext z
    simp only [coreFunction_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [heq]
  exact (sliceSubmodule G theta N).sum_mem (fun n _ =>
    (sliceSubmodule G theta N).smul_mem _ (occupationFunction_has_slices G theta N n))

/-- Every original homogeneous sector polynomial really lands in the
independently defined full physical carrier. -/
def sectorPhysical (G : Geometry) (theta : Twist) (N : ℕ)
    (p : MvPolynomial.homogeneousSubmodule (OrbitalIndex G theta) ℂ N) :
    PhysicalBosonCarrier G theta N :=
  ⟨sectorFunction G theta N p,
    (slices_iff_joint_and_boundary G theta N _).mp (coreFunction_has_slices G theta N p.val) |>.1,
    (slices_iff_joint_and_boundary G theta N _).mp (coreFunction_has_slices G theta N p.val) |>.2,
    coreFunction_permute_configuration G theta N p.val⟩

theorem sectorPhysical_apply (G : Geometry) (theta : Twist) (N : ℕ)
    (p : MvPolynomial.homogeneousSubmodule (OrbitalIndex G theta) ℂ N) :
    (sectorPhysical G theta N p).val = sectorFunction G theta N p := rfl

theorem sectorPhysical_bijective (G : Geometry) (theta : Twist) (N : ℕ) :
    Function.Bijective (sectorPhysical G theta N) := by
  constructor
  · intro p q h
    exact sectorFunction_injective G theta N (congrArg Subtype.val h)
  · intro f
    obtain ⟨p,hp⟩ := physical_sector_surjective G theta N f
    exact ⟨p, Subtype.ext hp⟩

/-- Two-sided equivalence to the independent carrier, before norm packaging. -/
def physicalSectorEquiv (G : Geometry) (theta : Twist) (N : ℕ) :
    MvPolynomial.homogeneousSubmodule (OrbitalIndex G theta) ℂ N ≃
      PhysicalBosonCarrier G theta N :=
  Equiv.ofBijective (sectorPhysical G theta N) (sectorPhysical_bijective G theta N)

/-- The exact original product-cell inner product on ALL carrier elements. -/
theorem physicalSectorEquiv_inner (G : Geometry) (theta : Twist) (N : ℕ)
    (f g : PhysicalBosonCarrier G theta N) :
    sectorInner G N f.val g.val =
      TorusLean.Boson.occupationInner (fun _ => 1)
        ((physicalSectorEquiv G theta N).symm f).val
        ((physicalSectorEquiv G theta N).symm g).val := by
  have h := sectorFunction_inner G theta N
    ((physicalSectorEquiv G theta N).symm f) ((physicalSectorEquiv G theta N).symm g)
  have hf : sectorFunction G theta N ((physicalSectorEquiv G theta N).symm f) = f.val :=
    congrArg Subtype.val ((physicalSectorEquiv G theta N).apply_symm_apply f)
  have hg : sectorFunction G theta N ((physicalSectorEquiv G theta N).symm g) = g.val :=
    congrArg Subtype.val ((physicalSectorEquiv G theta N).apply_symm_apply g)
  rw [hf,hg] at h
  exact h

theorem physicalSectorEquiv_normSq (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta N) :
    (∫ z, ‖f.val z‖^2 ∂sectorMeasure G N) =
      TorusLean.Boson.occupationMetricNormSq (fun _ => 1)
        ((physicalSectorEquiv G theta N).symm f).val := by
  have h := sectorFunction_normSq G theta N ((physicalSectorEquiv G theta N).symm f)
  have hf : sectorFunction G theta N ((physicalSectorEquiv G theta N).symm f) = f.val :=
    congrArg Subtype.val ((physicalSectorEquiv G theta N).apply_symm_apply f)
  rw [hf] at h
  exact h

#print axioms physicalSectorEquiv_normSq
#print axioms product_sections_has_slices
#print axioms wordFunction_has_slices
#print axioms symWordFunction_has_slices
#print axioms occupationFunction_has_slices
#print axioms coreFunction_has_slices
#print axioms sectorPhysical_apply
#print axioms sectorPhysical_bijective
#print axioms physicalSectorEquiv_inner

end TorusLean.Shared.PhysicalBosonMembership
