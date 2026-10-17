import torus.shared.PhysicalBosonFullContact
import torus.shared.ChargeTwoEvaluation

set_option autoImplicit false
noncomputable section

namespace TorusLean.Shared.PhysicalBosonPairBudget

open MeasureTheory TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.PhysicalBosonPolarization
open TorusLean.Shared.PhysicalBosonDiagonal TorusLean.Shared.PhysicalBosonContactForm
open TorusLean.Shared.PhysicalBosonFullContact TorusLean.Shared.ChargeTwoEvaluation
open TorusLean.Boson.PhysicalContactLiftCandidate
open TorusLean.Fermion.LatticePacking TorusLean.Fermion.LatticeLaguerreSum

local instance physicalOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (PhysicalBosonSector.OrbitalIndex G theta) :=
  ⟨⟨0, lll_finrank_pos G theta 1⟩⟩

theorem pairDiagonalFactor_ne_zero (N : ℕ) : pairDiagonalFactor N ≠ 0 := by
  unfold pairDiagonalFactor
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_ne_zero'.mpr
        (Nat.cast_pos.mpr (Nat.factorial_pos (N+2)))))
    · exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  · exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr
      (Nat.cast_pos.mpr (Nat.factorial_pos N)))

/-- Literal pair restriction with the unchanged normalized pair-removal
factor inherited from the original finite-sector convention. -/
def physicalPairFunction (G : Geometry) (theta : Twist) (N : ℕ)
    (R : ℂ) (f : PhysicalBosonCarrier G theta (N+2)) : (Fin N → ℂ) → ℂ :=
  fun z => (pairDiagonalFactor N)⁻¹ * f.val (insertDiagonal N (R,z))

theorem physicalPairFunction_eq_core (G : Geometry) (theta : Twist) (N : ℕ)
    (R : ℂ) (f : PhysicalBosonCarrier G theta (N+2)) :
    physicalPairFunction G theta N R f =
      coreFunction G theta N (modePair (evaluationCoordinates G theta R)
        ((physicalSectorEquiv G theta (N+2)).symm f).val) := by
  let p := (physicalSectorEquiv G theta (N+2)).symm f
  have hp : coreFunction G theta (N+2) p.val = f.val :=
    congrArg Subtype.val ((physicalSectorEquiv G theta (N+2)).apply_symm_apply f)
  funext z
  unfold physicalPairFunction
  rw [← hp]
  have h := coreFunction_diagonal_pair G theta N p.val (R,z)
  change coreFunction G theta (N+2) p.val (insertDiagonal N (R,z)) = _ at h
  rw [h]
  exact inv_mul_cancel_left₀ (pairDiagonalFactor_ne_zero N) _

theorem physicalPairFunction_normSq (G : Geometry) (theta : Twist) (N : ℕ)
    (R : ℂ) (f : PhysicalBosonCarrier G theta (N+2)) :
    (∫ z, ‖physicalPairFunction G theta N R f z‖^2 ∂sectorMeasure G N) =
      occupationMetricNormSq (fun _ => 1)
        (modePair (evaluationCoordinates G theta R)
          ((physicalSectorEquiv G theta (N+2)).symm f).val) := by
  rw [physicalPairFunction_eq_core]
  exact coreFunction_normSq G theta N _
    (modePair_sector _ N _ ((physicalSectorEquiv G theta (N+2)).symm f).property)

/-- A genuine N-independent geometric comparison for literal normalized
physical pair restriction, on every full independent physical sector. -/
theorem physicalPairFunction_geometric_bound (G : Geometry) (theta : Twist) (N : ℕ)
    (R : ℂ) (f : PhysicalBosonCarrier G theta (N+2))
    (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G) :
    (∫ z, ‖physicalPairFunction G theta N R f z‖^2 ∂sectorMeasure G N) ≤
      (1 + Real.exp (-L^2/4) * gaussianConstant) * actualParticleContactEnergy G (N+2) f.val := by
  rw [physicalPairFunction_normSq, fullCarrier_contact_energy_same_lift]
  let p := ((physicalSectorEquiv G theta (N+2)).symm f).val
  have h := rawRieszPair_le_contactCoreHamiltonian G theta R p
  change occupationMetricNormSq (fun _ => 1) (modePair (evaluationCoordinates G theta R) p) ≤
    ‖lllEvaluation G theta 2 R‖^2 *
      (occupationInner (fun _ => 1) p (contactCoreHamiltonian G theta p)).re at h
  apply h.trans
  apply mul_le_mul_of_nonneg_right _ (contactCoreHamiltonian_nonneg G theta p)
  have he := (abs_le.mp (evaluation_two_norm_sq_sub_one_le G theta R L hL1 hL)).2
  linarith

#print axioms pairDiagonalFactor_ne_zero
#print axioms physicalPairFunction_eq_core
#print axioms physicalPairFunction_normSq
#print axioms physicalPairFunction_geometric_bound

end TorusLean.Shared.PhysicalBosonPairBudget
