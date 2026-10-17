import torus.shared.PhysicalBosonMembership

set_option autoImplicit false
noncomputable section

namespace TorusLean.Shared.PhysicalBosonLinearEquiv

open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.LLLSliceReconstruction

/-- Pointwise linear operations preserve the independent physical predicate. -/
def physicalSubmodule (G : Geometry) (theta : Twist) (N : ℕ) :
    Submodule ℂ ((Fin N → ℂ) → ℂ) where
  carrier := {f | JointGaussianHolomorphic N f ∧ ParticleBoundary G theta N f ∧
    BosonSymmetric N f}
  zero_mem' := by
    have h := (slices_iff_joint_and_boundary G theta N 0).mp
      (sliceSubmodule G theta N).zero_mem
    exact ⟨h.1,h.2,fun _ _ => rfl⟩
  add_mem' := by
    intro f g hf hg
    have hs : HasLLLSlices G theta N (f+g) := (sliceSubmodule G theta N).add_mem
      ((slices_iff_joint_and_boundary G theta N f).mpr ⟨hf.1,hf.2.1⟩)
      ((slices_iff_joint_and_boundary G theta N g).mpr ⟨hg.1,hg.2.1⟩)
    have h := (slices_iff_joint_and_boundary G theta N (f+g)).mp hs
    refine ⟨h.1,h.2,?_⟩
    intro σ z
    exact congrArg₂ (·+·) (hf.2.2 σ z) (hg.2.2 σ z)
  smul_mem' := by
    intro c f hf
    have hs : HasLLLSlices G theta N (c • f) := (sliceSubmodule G theta N).smul_mem c
      ((slices_iff_joint_and_boundary G theta N f).mpr ⟨hf.1,hf.2.1⟩)
    have h := (slices_iff_joint_and_boundary G theta N (c • f)).mp hs
    refine ⟨h.1,h.2,?_⟩
    intro σ z
    exact congrArg (fun q : ℂ => c*q) (hf.2.2 σ z)

instance physicalAddCommGroup (G : Geometry) (theta : Twist) (N : ℕ) :
    AddCommGroup (PhysicalBosonCarrier G theta N) :=
  inferInstanceAs (AddCommGroup ↥(physicalSubmodule G theta N))

instance physicalModule (G : Geometry) (theta : Twist) (N : ℕ) :
    Module ℂ (PhysicalBosonCarrier G theta N) :=
  inferInstanceAs (Module ℂ ↥(physicalSubmodule G theta N))

def sectorPhysicalLinear (G : Geometry) (theta : Twist) (N : ℕ) :
    MvPolynomial.homogeneousSubmodule (OrbitalIndex G theta) ℂ N →ₗ[ℂ]
      PhysicalBosonCarrier G theta N where
  toFun := sectorPhysical G theta N
  map_add' p q := Subtype.ext ((sectorFunction G theta N).map_add p q)
  map_smul' c p := Subtype.ext ((sectorFunction G theta N).map_smul c p)

/-- Actual complex-linear equivalence with pointwise physical operations. -/
def physicalSectorLinearEquiv (G : Geometry) (theta : Twist) (N : ℕ) :
    MvPolynomial.homogeneousSubmodule (OrbitalIndex G theta) ℂ N ≃ₗ[ℂ]
      PhysicalBosonCarrier G theta N :=
  LinearEquiv.ofBijective (sectorPhysicalLinear G theta N) (sectorPhysical_bijective G theta N)

theorem physicalSectorLinearEquiv_apply (G : Geometry) (theta : Twist) (N : ℕ)
    (p : MvPolynomial.homogeneousSubmodule (OrbitalIndex G theta) ℂ N) :
    (physicalSectorLinearEquiv G theta N p).val = sectorFunction G theta N p := rfl

theorem physicalSectorLinearEquiv_toEquiv (G : Geometry) (theta : Twist) (N : ℕ) :
    (physicalSectorLinearEquiv G theta N).toEquiv = physicalSectorEquiv G theta N := by
  ext p
  rfl

#print axioms physicalSectorLinearEquiv_apply
#print axioms physicalSectorLinearEquiv_toEquiv

end TorusLean.Shared.PhysicalBosonLinearEquiv
