import torus.shared.BosonPairNearProjection
import torus.shared.BosonDoubleContraction
import torus.shared.PhysicalBosonSquare

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonDoubleContractionBudget
open TorusLean.Boson TorusLean.Boson.TwoBodyLift TorusLean.Boson.UnitaryTransport
open TorusLean.Boson.PhysicalContactLiftCandidate TorusLean.Boson.ContactHilbertBridge
open TorusLean.Shared.BosonPairNearProjection TorusLean.Shared.BosonDoubleContraction
open TorusLean.Shared.BosonPairContractions TorusLean.Shared.BosonLiftSquare
open TorusLean.Fermion.LatticePacking
local instance physicalOrbitalIndex_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0, lll_finrank_pos G theta 1⟩⟩

theorem contactPairCoordinates_transport (G : Geometry) (theta : Twist)
    (ψ : PairSpace (OrbitalIndex G theta)) :
    contactPairCoordinates G theta ψ =
      sym2Transport (physicalOrbitalCoordinates G theta)
        (bosonPairOperator G theta ((sym2Transport (physicalOrbitalCoordinates G theta)).symm ψ)) := by
  apply ext_inner_left ℂ
  intro φ
  rw [contactPairCoordinates_inner]
  have hu := LinearIsometryEquiv.inner_map_map (𝕜 := ℂ) (E := PairSpace (OrbitalIndex G theta))
    (E' := Sym2Evaluation.Sym2 (LLL G theta 1)) (sym2Transport (physicalOrbitalCoordinates G theta)).symm φ
    (sym2Transport (physicalOrbitalCoordinates G theta)
      (bosonPairOperator G theta ((sym2Transport (physicalOrbitalCoordinates G theta)).symm ψ)))
  simpa only [LinearIsometryEquiv.symm_apply_apply] using hu

theorem contactPairCoordinates_square_form (G : Geometry) (theta : Twist)
    (ψ : PairSpace (OrbitalIndex G theta)) :
    inner ℂ ψ (contactPairCoordinates G theta (contactPairCoordinates G theta ψ)) =
      inner ℂ ((sym2Transport (physicalOrbitalCoordinates G theta)).symm ψ)
        (bosonPairOperator G theta (bosonPairOperator G theta
          ((sym2Transport (physicalOrbitalCoordinates G theta)).symm ψ))) := by
  rw [contactPairCoordinates_inner, contactPairCoordinates_transport,
    LinearIsometryEquiv.symm_apply_apply]

theorem contactPairCoordinates_square_lower_positive (G : Geometry) (theta : Twist)
    (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G) :
    LinearMap.IsPositive (𝕜 := ℂ) (E := PairSpace (OrbitalIndex G theta))
      ((contactPairCoordinates G theta).comp (contactPairCoordinates G theta) -
        ((1-Real.exp (-L^2/8)*gaussianConstant : ℝ) : ℂ) • contactPairCoordinates G theta) := by
  let h := contactPairCoordinates G theta
  have hh : LinearMap.IsSymmetric (𝕜 := ℂ) (E := PairSpace (OrbitalIndex G theta)) h := (coordinatePairOperator_positive
    (physicalOrbitalCoordinates G theta) (contactQ G theta)).1
  have hh2 : LinearMap.IsSymmetric (𝕜 := ℂ) (E := PairSpace (OrbitalIndex G theta)) (h.comp h) := by
    intro u v
    change inner ℂ (h (h u)) v = inner ℂ u (h (h v))
    rw [hh, hh]
  refine ⟨hh2.sub (hh.smul (by exact Complex.conj_ofReal _)), ?_⟩
  intro ψ
  rw [inner_re_symm (𝕜 := ℂ)]
  change 0 ≤ (inner ℂ ψ (h (h ψ) -
    ((1-Real.exp (-L^2/8)*gaussianConstant : ℝ) : ℂ) • h ψ)).re
  rw [inner_sub_right, _root_.inner_smul_right (𝕜 := ℂ)
    (E := PairSpace (OrbitalIndex G theta)), Complex.sub_re, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  change 0 ≤ (inner ℂ ψ (contactPairCoordinates G theta (contactPairCoordinates G theta ψ))).re - _
  rw [contactPairCoordinates_square_form, contactPairCoordinates_inner]
  exact sub_nonneg.mpr (physical_pair_square_form_lower G theta L hL1 hL _)

theorem doubleContraction_core_lower (G : Geometry) (theta : Twist)
    (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G)
    (p : Core (OrbitalIndex G theta) ℂ) :
    (1-Real.exp (-L^2/8)*gaussianConstant) *
      (occupationInner (fun _ => 1) p (contactCoreHamiltonian G theta p)).re ≤
      (occupationInner (fun _ => 1) p
        (contractionLift (contactPairCoordinates G theta) doubleContraction p)).re := by
  have hb := twoBodyLift_order ((contactPairCoordinates G theta).comp (contactPairCoordinates G theta))
    (((1-Real.exp (-L^2/8)*gaussianConstant : ℝ) : ℂ) • contactPairCoordinates G theta)
    (contactPairCoordinates_square_lower_positive G theta L hL1 hL) p
  rw [twoBodyLift_smul, LinearMap.smul_apply, TwoBodyLift.inner_smul_right] at hb
  rw [doubleContractionLift_eq_square]
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    SpectatorControl.ip, contactCoreHamiltonian, coordinateHamiltonian, contactPairCoordinates] using hb

open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonMembership
open TorusLean.Shared.PhysicalBosonContactForm TorusLean.Shared.PhysicalBosonFullContact

theorem doubleContraction_fullCarrier_lower (G : Geometry) (theta : Twist)
    (L : ℝ) (hL1 : 1 ≤ L) (hL : L ≤ systole G) (N : ℕ)
    (f : PhysicalBosonCarrier G theta N) :
    (1-Real.exp (-L^2/8)*gaussianConstant) * actualParticleContactEnergy G N f.val ≤
      (occupationInner (fun _ => 1) ((physicalSectorEquiv G theta N).symm f).val
        (contractionLift (contactPairCoordinates G theta) doubleContraction
          ((physicalSectorEquiv G theta N).symm f).val)).re := by
  rw [fullCarrier_contact_energy_same_lift]
  exact doubleContraction_core_lower G theta L hL1 hL _

open TorusLean.Shared.BosonSystole20Scalar TorusLean.Shared.BosonSystole20Gram

/-- The manuscript's uniform double-contraction payment on every full
physical N-body state, using the same actual contact energy. -/
theorem doubleContraction_fullCarrier_twenty (G : Geometry) (theta : Twist)
    (hL : 20 ≤ systole G) (N : ℕ) (f : PhysicalBosonCarrier G theta N) :
    (1-allowance) * actualParticleContactEnergy G N f.val ≤
      (occupationInner (fun _ => 1) ((physicalSectorEquiv G theta N).symm f).val
        (contractionLift (contactPairCoordinates G theta) doubleContraction
          ((physicalSectorEquiv G theta N).symm f).val)).re := by
  have hb := doubleContraction_fullCarrier_lower G theta 20 (by norm_num) hL N f
  norm_num only [show -(20 : ℝ)^2/8 = -50 by norm_num] at hb
  have he : Real.exp (-50 : ℝ) ≤ 1/(2:ℝ)^72 := by
    convert (exp_neg_nat_mul_bound 72 (by decide)).le using 1; norm_num
  have heps : Real.exp (-50)*gaussianConstant ≤ allowance := by
    calc
      _ ≤ (1/(2:ℝ)^72)*8450 :=
        mul_le_mul he gaussianConstant_le gaussianConstant_nonneg (by positivity)
      _ ≤ _ := by norm_num [allowance]
  have henergy : 0 ≤ actualParticleContactEnergy G N f.val := by
    rw [fullCarrier_contact_energy_same_lift]
    exact contactCoreHamiltonian_nonneg G theta _
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_left heps 1) henergy).trans hb

#print axioms contactPairCoordinates_transport
#print axioms contactPairCoordinates_square_form
#print axioms contactPairCoordinates_square_lower_positive
#print axioms doubleContraction_core_lower
#print axioms doubleContraction_fullCarrier_lower
#print axioms doubleContraction_fullCarrier_twenty
end TorusLean.Shared.BosonDoubleContractionBudget
