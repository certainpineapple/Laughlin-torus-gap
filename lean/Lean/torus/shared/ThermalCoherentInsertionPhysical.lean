import torus.shared.ThermalCoherentInsertionAlgebra
import torus.shared.ThermalCoherentIntegral
import torus.shared.ThermalCoherentDoubleIntegral

/-! Normal-ordered coherent rank-one lifts on the same factorial core.
On the three- and four-particle sector they are the actual inserted seed's
rank-one operator. Their all-N quadratic forms are exactly the established
physical thermal integrands. No COM or infinite Omega identity is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentInsertionPhysical
open MeasureTheory TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Boson.SpectatorControl TorusLean.Boson.Sym2Evaluation
open TorusLean.Shared.ThermalCoherentInsertionAlgebra
open scoped TensorProduct

section Algebra
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def coherentThreeLift (u v : Orbital ι) : Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  (LinearMap.mulLeft ℂ (threeInsertion (symTensor u u ⊗ₜ[ℂ] v))).comp
    ((modeAnnihilate v).comp (modePair u))

def coherentFourLift (u v w : Orbital ι) : Core ι ℂ →ₗ[ℂ] Core ι ℂ :=
  (LinearMap.mulLeft ℂ (fourInsertion (symTensor u u ⊗ₜ[ℂ] symTensor v w))).comp
    (((Real.sqrt 2)⁻¹ : ℂ) • (spectatorPair v w).comp (modePair u))

theorem coherentThreeLift_inner (u v : Orbital ι) (p : Core ι ℂ) :
    (occupationInner (fun _ => 1) p (coherentThreeLift u v p)).re =
      occupationMetricNormSq (fun _ => 1) (modeAnnihilate v (modePair u p)) := by
  change (ip p (threeInsertion (symTensor u u ⊗ₜ[ℂ] v) * modeAnnihilate v (modePair u p))).re = _
  rw [canonical_inner_real_symm]
  simp only [ip]
  rw [threeInsertion_coherent_adjoint, occupationInner_self_re]

theorem coherentFourLift_inner (u v w : Orbital ι) (p : Core ι ℂ) :
    (occupationInner (fun _ => 1) p (coherentFourLift u v w p)).re =
      (1/2 : ℝ) * occupationMetricNormSq (fun _ => 1) (spectatorPair v w (modePair u p)) := by
  change (ip p (fourInsertion (symTensor u u ⊗ₜ[ℂ] symTensor v w) *
    normalizedDoubleRemoval u v w p)).re = _
  rw [canonical_inner_real_symm]
  simp only [ip]
  rw [fourInsertion_coherent_adjoint, occupationInner_self_re, normalizedDoubleRemoval_normSq]

theorem oneRemoval_threeSector (u v : Orbital ι) (p : Core ι ℂ)
    (hp : p.IsHomogeneous 3) : (modeAnnihilate v (modePair u p)).IsHomogeneous 0 :=
  modeAnnihilate_sector v 0 _ (modePair_sector u 1 p hp)

theorem normalizedDoubleRemoval_fourSector (u v w : Orbital ι) (p : Core ι ℂ)
    (hp : p.IsHomogeneous 4) : (normalizedDoubleRemoval u v w p).IsHomogeneous 0 := by
  have h := spectatorPair_sector v w 0 _ (modePair_sector u 2 p hp)
  simp only [normalizedDoubleRemoval, MvPolynomial.smul_eq_C_mul]
  exact h.C_mul _

/-- On the genuine three-particle sector this is exactly the rank-one map
of the actual finite tensor-insertion seed; it is not an arbitrary form definition. -/
theorem coherentThreeLift_threeSector (u v : Orbital ι) (p : Core ι ℂ)
    (hp : p.IsHomogeneous 3) :
    coherentThreeLift u v p =
      occupationInner (fun _ => 1) (threeInsertion (symTensor u u ⊗ₜ[ℂ] v)) p •
        threeInsertion (symTensor u u ⊗ₜ[ℂ] v) := by
  change threeInsertion (symTensor u u ⊗ₜ[ℂ] v) * modeAnnihilate v (modePair u p) = _
  rw [TwoBodyLift.homogeneous_zero_eq_vacuum _ (oneRemoval_threeSector u v p hp)]
  simp only [ip]
  rw [← threeInsertion_coherent_analysis]
  simp only [mul_smul_comm, mul_one]

/-- The four-particle rank-one coefficient retains the actual Sym² seed
and its full multiplicities, including repeated and nonorthogonal modes. -/
theorem coherentFourLift_fourSector (u v w : Orbital ι) (p : Core ι ℂ)
    (hp : p.IsHomogeneous 4) :
    coherentFourLift u v w p =
      occupationInner (fun _ => 1) (fourInsertion (symTensor u u ⊗ₜ[ℂ] symTensor v w)) p •
        fourInsertion (symTensor u u ⊗ₜ[ℂ] symTensor v w) := by
  change fourInsertion (symTensor u u ⊗ₜ[ℂ] symTensor v w) * normalizedDoubleRemoval u v w p = _
  rw [TwoBodyLift.homogeneous_zero_eq_vacuum _ (normalizedDoubleRemoval_fourSector u v w p hp)]
  simp only [ip]
  rw [← fourInsertion_coherent_analysis]
  simp only [mul_smul_comm, mul_one]

end Algebra

open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Shared.ThermalCoherentOccupation TorusLean.Shared.ThermalCoherentGaussian
open TorusLean.Shared.ThermalCoherentRegularity TorusLean.Shared.ThermalCoherentIntegral
open TorusLean.Shared.ThermalCoherentDoubleGaussian TorusLean.Shared.ThermalCoherentDoubleRegularity
open TorusLean.Shared.ThermalCoherentDoubleIntegral TorusLean.Fermion.PlaneMagneticUnitary

local instance physicalOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0, lll_finrank_pos G theta 1⟩⟩

/-- The inserted coherent seed is an element of the independently defined
full physical three-particle carrier, with no membership premise. -/
def physicalThreeInsertionSeed (G : Geometry) (theta : Twist) (R S : ℂ) :
    PhysicalBosonCarrier G theta 3 :=
  sectorPhysical G theta 3 ⟨threeInsertion
    (symTensor (evaluationCoordinates G theta R) (evaluationCoordinates G theta R) ⊗ₜ[ℂ]
      evaluationCoordinates G theta S), threeInsertion_sector _⟩

def physicalFourInsertionSeed (G : Geometry) (theta : Twist) (R S T : ℂ) :
    PhysicalBosonCarrier G theta 4 :=
  sectorPhysical G theta 4 ⟨fourInsertion
    (symTensor (evaluationCoordinates G theta R) (evaluationCoordinates G theta R) ⊗ₜ[ℂ]
      symTensor (evaluationCoordinates G theta S) (evaluationCoordinates G theta T)),
        fourInsertion_sector _⟩

theorem physicalThreeInsertionSeed_coordinates (G : Geometry) (theta : Twist) (R S : ℂ) :
    ((physicalSectorEquiv G theta 3).symm (physicalThreeInsertionSeed G theta R S)).val =
      threeInsertion (symTensor (evaluationCoordinates G theta R) (evaluationCoordinates G theta R)
        ⊗ₜ[ℂ] evaluationCoordinates G theta S) := by
  exact congrArg Subtype.val ((physicalSectorEquiv G theta 3).symm_apply_apply _)

theorem physicalFourInsertionSeed_coordinates (G : Geometry) (theta : Twist) (R S T : ℂ) :
    ((physicalSectorEquiv G theta 4).symm (physicalFourInsertionSeed G theta R S T)).val =
      fourInsertion (symTensor (evaluationCoordinates G theta R) (evaluationCoordinates G theta R)
        ⊗ₜ[ℂ] symTensor (evaluationCoordinates G theta S) (evaluationCoordinates G theta T)) := by
  exact congrArg Subtype.val ((physicalSectorEquiv G theta 4).symm_apply_apply _)

/-- Exact all-N annihilation row of the raw physical one-spectator seed. -/
theorem raw_threeInsertion_adjoint (G : Geometry) (theta : Twist) (R S : ℂ)
    (f p : Core (OrbitalIndex G theta) ℂ) :
    occupationInner (fun _ => 1)
      (((physicalSectorEquiv G theta 3).symm (physicalThreeInsertionSeed G theta R S)).val * f) p =
      occupationInner (fun _ => 1) f (modeAnnihilate (evaluationCoordinates G theta S)
        (modePair (evaluationCoordinates G theta R) p)) := by
  rw [physicalThreeInsertionSeed_coordinates]
  exact threeInsertion_coherent_adjoint _ _ f p

/-- Exact all-N annihilation row of the raw physical Sym²-spectator seed. -/
theorem raw_fourInsertion_adjoint (G : Geometry) (theta : Twist) (R S T : ℂ)
    (f p : Core (OrbitalIndex G theta) ℂ) :
    occupationInner (fun _ => 1)
      (((physicalSectorEquiv G theta 4).symm (physicalFourInsertionSeed G theta R S T)).val * f) p =
      occupationInner (fun _ => 1) f (normalizedDoubleRemoval (evaluationCoordinates G theta R)
        (evaluationCoordinates G theta S) (evaluationCoordinates G theta T) p) := by
  rw [physicalFourInsertionSeed_coordinates]
  exact fourInsertion_coherent_adjoint _ _ _ f p

/-- The one-spectator thermal integrand is the quadratic form of this
actual normal-ordered inserted rank-one seed on every finite core. -/
theorem oneSpectatorIntegrand_eq_coherentLift (G : Geometry) (theta : Twist) (a : ℝ)
    (p : Core (OrbitalIndex G theta) ℂ) (x : ℂ × ℂ) :
    oneSpectatorIntegrand G theta a p x = thermalWeight a x.2 *
      (occupationInner (fun _ => 1) p
        (coherentThreeLift (evaluationCoordinates G theta x.1)
          (evaluationCoordinates G theta (x.1+x.2)) p)).re := by
  rw [coherentThreeLift_inner]
  rfl

/-- The unique half factor in the accepted double thermal integrand now
follows from the actual Sym²/Fock seed and its derived annihilation row. -/
theorem twoSpectatorIntegrand_eq_coherentLift (G : Geometry) (theta : Twist) (a : ℝ)
    (p : Core (OrbitalIndex G theta) ℂ) (x : ℂ × (ℂ × ℂ)) :
    twoSpectatorIntegrand G theta a p x = thermalProductWeight a x.2 *
      (occupationInner (fun _ => 1) p
        (coherentFourLift (evaluationCoordinates G theta x.1)
          (evaluationCoordinates G theta (x.1+x.2.1))
          (evaluationCoordinates G theta (x.1+x.2.2)) p)).re := by
  rw [coherentFourLift_inner]
  rfl

#print axioms coherentThreeLift_inner
#print axioms coherentFourLift_inner
#print axioms coherentThreeLift_threeSector
#print axioms coherentFourLift_fourSector
#print axioms physicalThreeInsertionSeed_coordinates
#print axioms physicalFourInsertionSeed_coordinates
#print axioms raw_threeInsertion_adjoint
#print axioms raw_fourInsertion_adjoint
#print axioms oneSpectatorIntegrand_eq_coherentLift
#print axioms twoSpectatorIntegrand_eq_coherentLift
end TorusLean.Shared.ThermalCoherentInsertionPhysical
