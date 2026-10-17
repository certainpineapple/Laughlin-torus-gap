import torus.shared.BosonThreeBodyLiftContraction
import torus.shared.PhysicalBosonSquare

set_option autoImplicit false
noncomputable section
open scoped ComplexOrder
namespace TorusLean.Shared.BosonThreeBodyLiftPhysical
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.PhysicalBosonLinearEquiv
open TorusLean.Shared.PhysicalBosonOperator TorusLean.Shared.PhysicalBosonSquare
open TorusLean.Shared.BosonPairContractions TorusLean.Shared.BosonLiftSquare
open TorusLean.Shared.BosonThreeBodyLift TorusLean.Shared.BosonThreeBodyLiftContraction
open TorusLean.Shared.PhysicalBosonS4Coefficients
open TorusLean.Boson.PhysicalContactLiftCandidate
local instance physicalOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (PhysicalBosonSector.OrbitalIndex G theta) := ⟨⟨0, lll_finrank_pos G theta 1⟩⟩

/-- Coordinates of an operator on the independent, complete physical N=3 carrier. -/
def coordinateThreeOperator (G : Geometry) (theta : Twist)
    (A : PhysicalBosonCarrier G theta 3 →ₗ[ℂ] PhysicalBosonCarrier G theta 3) :
    ThreeSector (PhysicalBosonSector.OrbitalIndex G theta) →ₗ[ℂ]
      ThreeSector (PhysicalBosonSector.OrbitalIndex G theta) :=
  (physicalSectorLinearEquiv G theta 3).symm.toLinearMap.comp
    (A.comp (physicalSectorLinearEquiv G theta 3).toLinearMap)

/-- Standard normalized three-body lift on every full physical N-particle carrier. -/
def physicalThreeBodyLift (G : Geometry) (theta : Twist)
    (A : PhysicalBosonCarrier G theta 3 →ₗ[ℂ] PhysicalBosonCarrier G theta 3) (N : ℕ) :
    PhysicalBosonCarrier G theta N →ₗ[ℂ] PhysicalBosonCarrier G theta N :=
  (physicalSectorLinearEquiv G theta N).toLinearMap.comp
    ((sectorThreeBodyLift (coordinateThreeOperator G theta A) N).comp
      (physicalSectorLinearEquiv G theta N).symm.toLinearMap)

theorem physicalThreeBodyLift_coordinates (G : Geometry) (theta : Twist)
    (A : PhysicalBosonCarrier G theta 3 →ₗ[ℂ] PhysicalBosonCarrier G theta 3) (N : ℕ)
    (f : PhysicalBosonCarrier G theta N) :
    (physicalSectorLinearEquiv G theta N).symm (physicalThreeBodyLift G theta A N f) =
      sectorThreeBodyLift (coordinateThreeOperator G theta A) N
        ((physicalSectorLinearEquiv G theta N).symm f) :=
  (physicalSectorLinearEquiv G theta N).symm_apply_apply _

theorem physicalThreeBodyLift_inner (G : Geometry) (theta : Twist)
    (A : PhysicalBosonCarrier G theta 3 →ₗ[ℂ] PhysicalBosonCarrier G theta 3) (N : ℕ)
    (f g : PhysicalBosonCarrier G theta N) :
    sectorInner G N f.val (physicalThreeBodyLift G theta A N g).val =
      ip ((physicalSectorLinearEquiv G theta N).symm f).val
        (threeBodyLift (coordinateThreeOperator G theta A)
          ((physicalSectorLinearEquiv G theta N).symm g).val) := by
  have h := physicalSectorEquiv_inner G theta N f (physicalThreeBodyLift G theta A N g)
  rw [← physicalSectorLinearEquiv_toEquiv] at h
  change sectorInner G N f.val (physicalThreeBodyLift G theta A N g).val =
    ip ((physicalSectorLinearEquiv G theta N).symm f).val
      ((physicalSectorLinearEquiv G theta N).symm (physicalThreeBodyLift G theta A N g)).val at h
  rw [physicalThreeBodyLift_coordinates] at h
  exact h

theorem coordinateThreeOperator_inner (G : Geometry) (theta : Twist)
    (A : PhysicalBosonCarrier G theta 3 →ₗ[ℂ] PhysicalBosonCarrier G theta 3)
    (p q : ThreeSector (PhysicalBosonSector.OrbitalIndex G theta)) :
    ip p.val (coordinateThreeOperator G theta A q).val =
      sectorInner G 3 (physicalSectorLinearEquiv G theta 3 p).val
        (A (physicalSectorLinearEquiv G theta 3 q)).val := by
  have h := sectorFunction_inner G theta 3 p (coordinateThreeOperator G theta A q)
  change sectorInner G 3 (physicalSectorLinearEquiv G theta 3 p).val
    (physicalSectorLinearEquiv G theta 3 (coordinateThreeOperator G theta A q)).val = _ at h
  change sectorInner G 3 (physicalSectorLinearEquiv G theta 3 p).val
    (physicalSectorLinearEquiv G theta 3 ((physicalSectorLinearEquiv G theta 3).symm
      (A (physicalSectorLinearEquiv G theta 3 q)))).val = _ at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- Exact N=3 normalization on actual functions in the original product measure. -/
theorem physicalThreeBodyLift_three (G : Geometry) (theta : Twist)
    (A : PhysicalBosonCarrier G theta 3 →ₗ[ℂ] PhysicalBosonCarrier G theta 3) :
    physicalThreeBodyLift G theta A 3 = A := by
  apply LinearMap.ext
  intro f
  apply (physicalSectorLinearEquiv G theta 3).symm.injective
  rw [physicalThreeBodyLift_coordinates]
  apply Subtype.ext
  change threeBodyLift (coordinateThreeOperator G theta A)
    ((physicalSectorLinearEquiv G theta 3).symm f).val = _
  rw [threeBodyLift_threeSector]
  simp only [coordinateThreeOperator, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply]

/-- Positivity on the actual complete N=3 carrier lifts to every actual N sector. -/
theorem physicalThreeBodyLift_nonneg (G : Geometry) (theta : Twist)
    (A : PhysicalBosonCarrier G theta 3 →ₗ[ℂ] PhysicalBosonCarrier G theta 3)
    (hA : ∀ p : PhysicalBosonCarrier G theta 3, 0 ≤ (sectorInner G 3 p.val (A p).val).re)
    (N : ℕ) (f : PhysicalBosonCarrier G theta N) :
    0 ≤ (sectorInner G N f.val (physicalThreeBodyLift G theta A N f).val).re := by
  rw [physicalThreeBodyLift_inner]
  apply threeBodyLift_nonneg
  intro p
  rw [coordinateThreeOperator_inner]
  exact hA _

/-- Quadratic-form order is preserved with no N-dependent comparison assumption. -/
theorem physicalThreeBodyLift_mono (G : Geometry) (theta : Twist)
    (A B : PhysicalBosonCarrier G theta 3 →ₗ[ℂ] PhysicalBosonCarrier G theta 3)
    (hAB : ∀ p : PhysicalBosonCarrier G theta 3,
      (sectorInner G 3 p.val (A p).val).re ≤ (sectorInner G 3 p.val (B p).val).re)
    (N : ℕ) (f : PhysicalBosonCarrier G theta N) :
    (sectorInner G N f.val (physicalThreeBodyLift G theta A N f).val).re ≤
      (sectorInner G N f.val (physicalThreeBodyLift G theta B N f).val).re := by
  rw [physicalThreeBodyLift_inner, physicalThreeBodyLift_inner]
  apply threeBodyLift_mono
  intro p
  rw [coordinateThreeOperator_inner, coordinateThreeOperator_inner]
  exact hAB _

/-- A finite PSD certificate applies to the canonical compressed matrix of the
actual physical three-particle operator. Identifying an external certificate
matrix with this kernel remains a separate mathematical obligation. -/
theorem physicalThreeBodyLift_nonneg_of_kernel_posSemidef (G : Geometry) (theta : Twist)
    (A : PhysicalBosonCarrier G theta 3 →ₗ[ℂ] PhysicalBosonCarrier G theta 3)
    (hK : (threeSectorKernel (coordinateThreeOperator G theta A)).PosSemidef)
    (N : ℕ) (f : PhysicalBosonCarrier G theta N) :
    0 ≤ (sectorInner G N f.val (physicalThreeBodyLift G theta A N f).val).re := by
  rw [physicalThreeBodyLift_inner]
  exact tripleCoefficientLift_nonneg _ hK _


/-- The actual same-contact single-contraction operator restricted to N=3. -/
def physicalSingleContractionThree (G : Geometry) (theta : Twist) :
    PhysicalBosonCarrier G theta 3 →ₗ[ℂ] PhysicalBosonCarrier G theta 3 :=
  (physicalSectorLinearEquiv G theta 3).toLinearMap.comp
    ((singleContractionThreeSector (contactPairCoordinates G theta)).comp
      (physicalSectorLinearEquiv G theta 3).symm.toLinearMap)

theorem physicalSingleContractionThree_coordinates (G : Geometry) (theta : Twist) :
    coordinateThreeOperator G theta (physicalSingleContractionThree G theta) =
      singleContractionThreeSector (contactPairCoordinates G theta) := by
  apply LinearMap.ext
  intro p
  simp only [coordinateThreeOperator, physicalSingleContractionThree,
    LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply]

/-- Exact identification of the single-contraction form in the physical H-square
with the standard lift of that same physical three-particle operator. -/
theorem physicalSingleContraction_lift_inner (G : Geometry) (theta : Twist) (N : ℕ)
    (f g : PhysicalBosonCarrier G theta N) :
    sectorInner G N f.val
      (physicalThreeBodyLift G theta (physicalSingleContractionThree G theta) N g).val =
      ip ((physicalSectorLinearEquiv G theta N).symm f).val
        (contractionLift (contactPairCoordinates G theta) singleContraction
          ((physicalSectorLinearEquiv G theta N).symm g).val) := by
  rw [physicalThreeBodyLift_inner, physicalSingleContractionThree_coordinates,
    ← singleContraction_eq_threeBodyLift]

/-- Actual physical H² with its three-body term now identified as an actual
N=3 operator lifted to all N. This identity itself asserts no three-body bound. -/
theorem physical_contact_square_threeBodyLift (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta N) :
    sectorInner G N f.val
      (transportedContactHamiltonian G theta N (transportedContactHamiltonian G theta N f)).val =
      normalOrderedFourBodyForm G theta ((physicalSectorLinearEquiv G theta N).symm f).val +
        sectorInner G N f.val
          (physicalThreeBodyLift G theta (physicalSingleContractionThree G theta) N f).val +
        occupationInner (fun _ => 1) ((physicalSectorLinearEquiv G theta N).symm f).val
          (contractionLift (contactPairCoordinates G theta) doubleContraction
            ((physicalSectorLinearEquiv G theta N).symm f).val) := by
  rw [physicalSingleContraction_lift_inner]
  exact physical_contact_square_form G theta N f

#print axioms physicalThreeBodyLift_coordinates
#print axioms physicalThreeBodyLift_inner
#print axioms coordinateThreeOperator_inner
#print axioms physicalThreeBodyLift_three
#print axioms physicalThreeBodyLift_nonneg
#print axioms physicalThreeBodyLift_mono
#print axioms physicalThreeBodyLift_nonneg_of_kernel_posSemidef
#print axioms physicalSingleContractionThree_coordinates
#print axioms physicalSingleContraction_lift_inner
#print axioms physical_contact_square_threeBodyLift

end TorusLean.Shared.BosonThreeBodyLiftPhysical
