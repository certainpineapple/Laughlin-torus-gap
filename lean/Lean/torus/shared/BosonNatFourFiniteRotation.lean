import torus.shared.BosonNatFourAnnihilator

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNatFourFiniteRotation
open TorusLean.Boson TorusLean.Boson.TwoBodyLift TorusLean.Boson.SpectatorControl
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.ThermalCoherentFourBodyFrame
open TorusLean.Shared.BosonAnchoredNatLinearActions TorusLean.Shared.BosonNatFourAnnihilator
open scoped BigOperators ComplexConjugate
local instance fourRotation_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

theorem natFourAnnihilator_cross_expansion (G : Geometry) (theta : Twist)
    (p r : Core ℕ ℂ) (R : ℂ) (f g : Core (OrbitalIndex G theta) ℂ) :
    ip (natFourAnnihilator G theta R p f) (natFourAnnihilator G theta R r g) =
      ∑ a, ∑ b, ip (quadRemove a f) (quadRemove b g) *
        (conj (seedDualMapNat G theta (quadVacuum b).val r R) *
          seedDualMapNat G theta (quadVacuum a).val p R) := by
  simp only [natFourAnnihilator,LinearMap.coe_mk,AddHom.coe_mk,
    LinearMap.sum_apply,LinearMap.smul_apply]
  rw [inner_sum_left]
  simp only [inner_sum_right,TwoBodyLift.inner_smul_left,TwoBodyLift.inner_smul_right,
    starRingEnd_apply,star_star]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- A genuine finite scalar cross-Parseval identity transports through the
actual antlinear annihilation map. This is a finite algebraic lemma, not an
isometry premise on the physical insertion. -/
theorem finite_annihilator_cross_congr {ι κ : Type*} (G : Geometry) (theta : Twist)
    (s : Finset ι) (t : Finset κ) (p : ι → Core ℕ ℂ) (r : κ → Core ℕ ℂ)
    (h : ∀ F H : Core ℕ ℂ →ₗ[ℂ] ℂ,
      (∑ i ∈ s, conj (F (p i)) * H (p i)) = ∑ j ∈ t, conj (F (r j)) * H (r j))
    (R : ℂ) (f g : Core (OrbitalIndex G theta) ℂ) :
    (∑ i ∈ s, ip (natFourAnnihilator G theta R (p i) f)
      (natFourAnnihilator G theta R (p i) g)) =
    ∑ j ∈ t, ip (natFourAnnihilator G theta R (r j) f)
      (natFourAnnihilator G theta R (r j) g) := by
  simp_rw [natFourAnnihilator_cross_expansion]
  rw [Finset.sum_comm (s := s),Finset.sum_comm (s := t)]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm (s := s),Finset.sum_comm (s := t)]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← Finset.mul_sum,← Finset.mul_sum]
  congr 1
  exact h ((LinearMap.proj R).comp (seedDualMapNat G theta (quadVacuum b).val))
    ((LinearMap.proj R).comp (seedDualMapNat G theta (quadVacuum a).val))

end TorusLean.Shared.BosonNatFourFiniteRotation
