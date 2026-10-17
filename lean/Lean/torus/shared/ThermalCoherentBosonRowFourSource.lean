import torus.shared.ThermalCoherentBosonRowSource
import torus.shared.BosonNatFourAnnihilator

/-! The zero-contraction CCR term is an actual four-particle source rank
cross on the original full core. Its creator/annihilator indices cross in
exactly the prescribed order. Original M4 coefficient identification is a
separate finite source calculation, not inferred from this naming. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRows
open TorusLean.Geometry TorusLean.Boson TorusLean.Boson.UnitaryTransport TorusLean.Boson.SpectatorControl
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonPeriodizedSeedNat
open TorusLean.Shared.BosonNatThreeAnnihilator TorusLean.Shared.BosonNatThreeRemovalTrace
open TorusLean.Shared.BosonNatFourAnnihilator TorusLean.Shared.BosonNatFourRemovalTrace
open TorusLean.Shared.BosonNormalizedNatSeeds TorusLean.Shared.BosonAnchoredTripleRows
open TorusLean.Shared.ThermalCoherentFourBodyLift TorusLean.Shared.BosonThreeBodyLift
open TorusLean.Shared.ThermalCoherentSpectralOccupation TorusLean.Shared.ThermalCoherentBosonRowCCR
open scoped BigOperators
local instance rowFourSource_nonempty (G : Geometry) (theta : Twist) : Nonempty (OrbitalIndex G theta) :=
  ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

/-- Actual four-source multiplication adjoint on the full core. -/
theorem natFourAnnihilator_creation_adjoint (G : Geometry) (theta : Twist) (R : ℂ)
    (p : Core ℕ ℂ) (hp : p.IsHomogeneous 4)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    ip (anchoredSeedNat G theta R p*f) g = ip f (natFourAnnihilator G theta R p g) := by
  rw [natFourAnnihilator_ground G theta p hp R]
  simpa only [natFourRemoval,natFourSeed,normalizedNatSeed_zero] using
    fourSeedRemoval_adjoint (natFourSeed G theta p hp 0 R) f g

/-- Adding a canonical source spectator adds precisely one raw annihilator. -/
theorem natFourAnnihilator_mul_spectator (G : Geometry) (theta : Twist) (R : ℂ)
    (p : Core ℕ ℂ) (hp : p.IsHomogeneous 3) (j : ℕ)
    (g : Core (OrbitalIndex G theta) ℂ) :
    natFourAnnihilator G theta R (p*MvPolynomial.X j) g =
      modeAnnihilate (rawJetMode G theta j R) (natThreeAnnihilator G theta R p g) := by
  apply ip_ext_right
  intro f
  rw [←natFourAnnihilator_creation_adjoint G theta R _
    (hp.mul (MvPolynomial.isHomogeneous_X ℂ j)),map_mul,anchoredSeedNat_X]
  change ip ((anchoredSeedNat G theta R p*modeLinear (rawJetMode G theta j R))*f) g = _
  rw [mul_assoc,←modeCreate_apply,natThreeAnnihilator_creation_adjoint G theta R p hp]
  exact mode_create_adjoint _ _ _

/-- Exact crossed-source form of the all-core bosonic zero-contraction term. -/
theorem actualRowFourCross_eq_source (G : Geometry) (theta : Twist) (ρ : RowIndex)
    (R : ℂ) (f g : Core (OrbitalIndex G theta) ℂ) :
    actualRowFourCross G theta ρ R f g =
      ∑ i : Fin 9, ∑ j : Fin 9,
        ip (natFourAnnihilator G theta R (rowThreeAuxiliarySeed ρ i*MvPolynomial.X j.val) f)
          (natFourAnnihilator G theta R (rowThreeAuxiliarySeed ρ j*MvPolynomial.X i.val) g) := by
  simp only [actualRowFourCross,rowFourCross,actualRowGrouped_eq_source,
    natFourAnnihilator_mul_spectator G theta R _ (rowThreeAuxiliarySeed_sector ρ _)]

end TorusLean.Shared.ThermalCoherentBosonRows
