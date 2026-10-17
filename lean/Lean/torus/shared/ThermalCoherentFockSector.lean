import torus.shared.PhysicalBosonOperator
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! The actual physical boson sector with its original product-cell Hilbert
norm. The construction uses the already proved full-carrier equivalence and
positive factorial occupation metric. Each unchanged contact Hamiltonian is
then a continuous self-adjoint positive block. No bound uniform in particle
number and no completed Fock operator are asserted in this file. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFockSector
open MeasureTheory TorusLean.Boson
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.PhysicalBosonLinearEquiv
open TorusLean.Shared.PhysicalBosonOperator TorusLean.Shared.PhysicalBosonContactForm

/-- Transport only of the already identified physical inner product. -/
@[instance_reducible]
def physicalInnerCore (G : Geometry) (theta : Twist) (N : ℕ) :
    InnerProductSpace.Core ℂ (PhysicalBosonCarrier G theta N) where
  inner f g := occupationInner (fun _ => 1)
    ((physicalSectorLinearEquiv G theta N).symm f).val
    ((physicalSectorLinearEquiv G theta N).symm g).val
  conj_inner_symm f g := occupationInner_conj_symm (fun _ => 1) _ _
  re_inner_nonneg f := occupationInner_self_nonneg (fun _ => 1) _
  add_left f g h := by
    simp only [map_add,Submodule.coe_add,occupationInner_add_left]
  smul_left f g c := by
    simp only [map_smul,Submodule.coe_smul,occupationInner_smul_left]
    rfl
  definite f hf := by
    apply (physicalSectorLinearEquiv G theta N).symm.injective
    apply Subtype.ext
    simpa only [map_zero,ZeroMemClass.coe_zero] using
      (occupationInner_self_eq_zero_iff (fun _ => 1) (fun _ => by omega) _).mp hf

private instance physicalCoreInstance (G : Geometry) (theta : Twist) (N : ℕ) :
    InnerProductSpace.Core ℂ (PhysicalBosonCarrier G theta N) := physicalInnerCore G theta N

instance physicalNormedAddCommGroup (G : Geometry) (theta : Twist) (N : ℕ) :
    NormedAddCommGroup (PhysicalBosonCarrier G theta N) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (PhysicalBosonCarrier G theta N) _ _ _
    (physicalInnerCore G theta N)

instance physicalInnerProductSpace (G : Geometry) (theta : Twist) (N : ℕ) :
    InnerProductSpace ℂ (PhysicalBosonCarrier G theta N) :=
  InnerProductSpace.ofCore
    (inferInstance : PreInnerProductSpace.Core ℂ (PhysicalBosonCarrier G theta N))

instance physicalNormedSpace (G : Geometry) (theta : Twist) (N : ℕ) :
    NormedSpace ℂ (PhysicalBosonCarrier G theta N) :=
  (physicalInnerProductSpace G theta N).toNormedSpace

/-- No new normalization: the inner product is exactly the original cell integral. -/
theorem physical_inner_eq_sectorInner (G : Geometry) (theta : Twist) (N : ℕ)
    (f g : PhysicalBosonCarrier G theta N) :
    inner ℂ f g = sectorInner G N f.val g.val := by
  change occupationInner (fun _ => 1)
    ((physicalSectorLinearEquiv G theta N).symm f).val
    ((physicalSectorLinearEquiv G theta N).symm g).val = _
  have h := physicalSectorEquiv_inner G theta N f g
  rw [← physicalSectorLinearEquiv_toEquiv] at h
  exact h.symm

/-- The Hilbert norm uses the same labelled product measure, including vacuum. -/
theorem physical_norm_sq_eq_sectorIntegral (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta N) :
    ‖f‖^2 = ∫ z, ‖f.val z‖^2 ∂sectorMeasure G N := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) f,
    physical_inner_eq_sectorInner]
  exact sectorInner_self_re G N f.val

instance physicalFiniteDimensional (G : Geometry) (theta : Twist) (N : ℕ) :
    FiniteDimensional ℂ (PhysicalBosonCarrier G theta N) := by
  letI : Module.Finite ℂ (MvPolynomial.homogeneousSubmodule (OrbitalIndex G theta) ℂ N) :=
    Module.Finite.iff_fg.mpr (MvPolynomial.homogeneousSubmodule_fg (OrbitalIndex G theta) ℂ N)
  exact (physicalSectorLinearEquiv G theta N).finiteDimensional

instance physicalCompleteSpace (G : Geometry) (theta : Twist) (N : ℕ) :
    CompleteSpace (PhysicalBosonCarrier G theta N) :=
  FiniteDimensional.complete ℂ (PhysicalBosonCarrier G theta N)

/-- Finite-dimensional continuity of the unchanged full-carrier contact block. -/
def actualSectorHamiltonian (G : Geometry) (theta : Twist) (N : ℕ) :
    PhysicalBosonCarrier G theta N →L[ℂ] PhysicalBosonCarrier G theta N :=
  (transportedContactHamiltonian G theta N).toContinuousLinearMap

theorem actualSectorHamiltonian_apply (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta N) :
    actualSectorHamiltonian G theta N f = transportedContactHamiltonian G theta N f := rfl

/-- The exact original particle-pair energy, not a replacement operator. -/
theorem actualSectorHamiltonian_energy (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta N) :
    (inner ℂ f (actualSectorHamiltonian G theta N f)).re =
      actualParticleContactEnergy G N f.val := by
  rw [physical_inner_eq_sectorInner,actualSectorHamiltonian_apply]
  exact transportedContactHamiltonian_energy G theta N f

theorem actualSectorHamiltonian_nonneg (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta N) :
    0 ≤ (inner ℂ f (actualSectorHamiltonian G theta N f)).re := by
  rw [physical_inner_eq_sectorInner,actualSectorHamiltonian_apply]
  exact transportedContactHamiltonian_nonneg G theta N f

/-- Every physical particle block is genuinely self-adjoint in its physical norm. -/
theorem actualSectorHamiltonian_selfAdjoint (G : Geometry) (theta : Twist) (N : ℕ) :
    IsSelfAdjoint (actualSectorHamiltonian G theta N) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro f g
  change inner ℂ (actualSectorHamiltonian G theta N f) g =
    inner ℂ f (actualSectorHamiltonian G theta N g)
  simp only [physical_inner_eq_sectorInner,actualSectorHamiltonian_apply]
  exact transportedContactHamiltonian_symmetric G theta N f g

end TorusLean.Shared.ThermalCoherentFockSector
