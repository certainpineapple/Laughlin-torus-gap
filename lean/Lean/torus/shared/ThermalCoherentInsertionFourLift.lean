import torus.shared.ThermalCoherentFourBodyLift
import torus.shared.ThermalCoherentInsertionPhysical
import torus.shared.PhysicalBosonS4Positive

/-! Actual normalized L4 matching for the coherent Sym² insertion, and an
independent normalization check against the existing same-H positive S4.
No planar COM/Weyl or infinite thermal transfer identity is supplied here. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentInsertionFourLift
open TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Boson.SpectatorControl TorusLean.Boson.Sym2Evaluation
open TorusLean.Shared.BosonThreeBodyLift
open TorusLean.Shared.ThermalCoherentFourBodyFrame TorusLean.Shared.ThermalCoherentFourBodyLift
open TorusLean.Shared.ThermalCoherentInsertionAlgebra
open TorusLean.Shared.ThermalCoherentInsertionPhysical
open scoped TensorProduct BigOperators

section Algebra
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def coherentFourSector (u v w : Orbital ι) : FourSector ι :=
  ⟨fourInsertion (symTensor u u ⊗ₜ[ℂ] symTensor v w), fourInsertion_sector _⟩

/-- The actual normalized annihilation row follows by adjoint uniqueness,
including arbitrary nonorthogonal or repeated spectator modes. -/
theorem fourSeedRemoval_coherent (u v w : Orbital ι) :
    fourSeedRemoval (coherentFourSector u v w) =
      ((Real.sqrt 2)⁻¹ : ℂ) • (spectatorPair v w).comp (modePair u) := by
  apply LinearMap.ext
  intro p
  apply ip_ext_right
  intro f
  rw [← fourSeedRemoval_adjoint]
  exact fourInsertion_coherent_adjoint u v w f p

/-- Whole-core identity of normalized L4 with the established coherent form. -/
theorem fourBodyLift_coherent_rankOne (u v w : Orbital ι) :
    fourBodyLift (fourSeedRankOne (coherentFourSector u v w) (coherentFourSector u v w)) =
      coherentFourLift u v w := by
  apply LinearMap.ext
  intro p
  rw [fourBodyLift_fourSeedRankOne_apply, fourSeedRemoval_coherent]
  rfl

end Algebra

open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Shared.ThermalCoherentDoubleGaussian TorusLean.Shared.ThermalCoherentDoubleIntegral
open TorusLean.Shared.PhysicalBosonS4 TorusLean.Shared.PhysicalBosonS4Coefficients
open TorusLean.Shared.PhysicalBosonS4Positive TorusLean.Shared.PhysicalBosonAnchor

local instance physicalOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0, lll_finrank_pos G theta 1⟩⟩

theorem coherentFourSector_eq_physicalSeed (G : Geometry) (theta : Twist) (R S T : ℂ) :
    coherentFourSector (evaluationCoordinates G theta R)
      (evaluationCoordinates G theta S) (evaluationCoordinates G theta T) =
      (physicalSectorEquiv G theta 4).symm (physicalFourInsertionSeed G theta R S T) := by
  apply Subtype.ext
  exact (physicalFourInsertionSeed_coordinates G theta R S T).symm

theorem twoSpectatorIntegrand_eq_fourBodyLift (G : Geometry) (theta : Twist) (a : ℝ)
    (p : Core (OrbitalIndex G theta) ℂ) (x : ℂ × (ℂ × ℂ)) :
    twoSpectatorIntegrand G theta a p x = thermalProductWeight a x.2 *
      (occupationInner (fun _ => 1) p
        (fourBodyLift (fourSeedRankOne
          (coherentFourSector (evaluationCoordinates G theta x.1)
            (evaluationCoordinates G theta (x.1+x.2.1)) (evaluationCoordinates G theta (x.1+x.2.2)))
          (coherentFourSector (evaluationCoordinates G theta x.1)
            (evaluationCoordinates G theta (x.1+x.2.1)) (evaluationCoordinates G theta (x.1+x.2.2)))) p)).re := by
  rw [fourBodyLift_coherent_rankOne]
  exact twoSpectatorIntegrand_eq_coherentLift G theta a p x

theorem twoSpectatorIntegrand_eq_physicalFourBodyLift (G : Geometry) (theta : Twist) (a : ℝ)
    (p : Core (OrbitalIndex G theta) ℂ) (x : ℂ × (ℂ × ℂ)) :
    twoSpectatorIntegrand G theta a p x = thermalProductWeight a x.2 *
      (occupationInner (fun _ => 1) p
        (fourBodyLift (fourSeedRankOne
          ((physicalSectorEquiv G theta 4).symm (physicalFourInsertionSeed G theta x.1
            (x.1+x.2.1) (x.1+x.2.2)))
          ((physicalSectorEquiv G theta 4).symm (physicalFourInsertionSeed G theta x.1
            (x.1+x.2.1) (x.1+x.2.2)))) p)).re := by
  rw [← coherentFourSector_eq_physicalSeed]
  exact twoSpectatorIntegrand_eq_fourBodyLift G theta a p x

/-- Original pair coefficients rewritten in the normalized ordered-four frame.
The proved factor six is 4!/(2! 2!), not a change to physical S4. -/
def contactQuadKernel (G : Geometry) (theta : Twist) :
    Matrix (QuadIndex (OrbitalIndex G theta)) (QuadIndex (OrbitalIndex G theta)) ℂ :=
  fun x y => (6 : ℂ) *
    (TwoBodyLift.pairKernel (PhysicalContactLiftCandidate.contactPairCoordinates G theta) x.1 y.1 *
      TwoBodyLift.pairKernel (PhysicalContactLiftCandidate.contactPairCoordinates G theta) x.2 y.2)

theorem contactQuadKernel_lift (G : Geometry) (theta : Twist) :
    quadCoefficientLift (contactQuadKernel G theta) = fourBodyCoreOperator G theta := by
  apply LinearMap.ext
  intro p
  have sum_quad (F : QuadIndex (OrbitalIndex G theta) → Core (OrbitalIndex G theta) ℂ) :
      (∑ x, F x) = ∑ a : TwoBodyLift.PairIndex (OrbitalIndex G theta),
        ∑ c : TwoBodyLift.PairIndex (OrbitalIndex G theta), F (a,c) :=
    Fintype.sum_prod_type F
  simp only [quadCoefficientLift, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply]
  simp_rw [sum_quad]
  simp only [contactQuadKernel, fourBodyCoreOperator, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, doublePair_eq_six_quad, smul_smul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro d hd
  congr 1
  ring

/-- A genuine four-particle operator whose coordinates are exactly the prior
S4 normal order on the four-sector, as verified by the next theorem. -/
def contactFourSector (G : Geometry) (theta : Twist) :
    FourSector (OrbitalIndex G theta) →ₗ[ℂ] FourSector (OrbitalIndex G theta) :=
  coefficientFourSector (contactQuadKernel G theta)

theorem contactFourSector_apply (G : Geometry) (theta : Twist)
    (f : FourSector (OrbitalIndex G theta)) :
    (contactFourSector G theta f).val = fourBodyCoreOperator G theta f.val := by
  rw [contactFourSector, coefficientFourSector_apply, contactQuadKernel_lift]

/-- Normalized L4 of the actual S4 four-sector restriction recovers exactly
its prior all-core operator, without any new scalar or N-dependent factor. -/
theorem fourBodyLift_contactFourSector (G : Geometry) (theta : Twist) :
    fourBodyLift (contactFourSector G theta) = fourBodyCoreOperator G theta := by
  rw [contactFourSector, fourBodyLift_restriction, contactQuadKernel_lift]

theorem actual_S4_eq_fourBodyLift (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalBosonCarrier G theta ((N+2)+2)) :
    actualPositiveFourBodyForm G theta N f =
      (occupationInner (fun _ => 1) ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val
        (fourBodyLift (contactFourSector G theta)
          ((physicalSectorEquiv G theta ((N+2)+2)).symm f).val)).re := by
  rw [fourBodyLift_contactFourSector, fourBodyCoreOperator_inner]
  exact actual_S4_eq_normalOrderedFourBodyForm G theta N f

end TorusLean.Shared.ThermalCoherentInsertionFourLift
