import torus.shared.BosonThermalJacobiRows
import torus.shared.ThermalCoherentJacobiPair

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonAnchoredTripleRows
open TorusLean.Boson TorusLean.Boson.UnitaryTransport TorusLean.Boson.SpectatorControl
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonPeriodizedSeedNat
open TorusLean.Shared.BosonNatThreeAnnihilator TorusLean.Shared.BosonNatThreeRemovalTrace
open TorusLean.Shared.BosonNormalizedNatSeeds TorusLean.Shared.ThermalCoherentInsertionThreeLift
open TorusLean.Shared.ThermalCoherentSpectralOccupation
open scoped BigOperators ComplexConjugate
local instance tripleRows_nonempty (G : Geometry) (theta : Twist) :
    Nonempty (OrbitalIndex G theta) := ⟨⟨0,lll_finrank_pos G theta 1⟩⟩

/-- The actual Nat seed row is the multiplication adjoint of its original
periodized polynomial, on all finite physical cores. -/
theorem natThreeAnnihilator_creation_adjoint (G : Geometry) (theta : Twist) (R : ℂ)
    (p : Core ℕ ℂ) (hp : p.IsHomogeneous 3)
    (f g : Core (OrbitalIndex G theta) ℂ) :
    ip (anchoredSeedNat G theta R p * f) g =
      ip f (natThreeAnnihilator G theta R p g) := by
  rw [natThreeAnnihilator_ground G theta p hp R]
  simpa only [natThreeRemoval,natThreeSeed,normalizedNatSeed_zero] using
    threeSeedRemoval_adjoint (natThreeSeed G theta p hp 0 R) f g

/-- No factorial is inserted for repeated labels: source monomials are
canonical creation words, and their adjoints are the actual ordered modes. -/
theorem natThreeAnnihilator_triple (G : Geometry) (theta : Twist) (R : ℂ)
    (i j k : ℕ) (g : Core (OrbitalIndex G theta) ℂ) :
    natThreeAnnihilator G theta R
      ((MvPolynomial.X i * MvPolynomial.X j) * MvPolynomial.X k) g =
      modeAnnihilate (rawJetMode G theta k R)
        (modeAnnihilate (rawJetMode G theta j R)
          (modeAnnihilate (rawJetMode G theta i R) g)) := by
  have hp : ((MvPolynomial.X i * MvPolynomial.X j) * MvPolynomial.X k : Core ℕ ℂ).IsHomogeneous 3 :=
    ((MvPolynomial.isHomogeneous_X ℂ i).mul (MvPolynomial.isHomogeneous_X ℂ j)).mul
      (MvPolynomial.isHomogeneous_X ℂ k)
  apply TorusLean.Shared.BosonThreeBodyLift.ip_ext_right
  intro f
  rw [← natThreeAnnihilator_creation_adjoint G theta R _ hp]
  simp only [map_mul,anchoredSeedNat_X]
  change ip (((modeLinear (rawJetMode G theta i R) * modeLinear (rawJetMode G theta j R)) *
      modeLinear (rawJetMode G theta k R)) * f) g = _
  have hc : ((modeLinear (rawJetMode G theta i R) * modeLinear (rawJetMode G theta j R)) *
      modeLinear (rawJetMode G theta k R)) * f =
      modeCreate (rawJetMode G theta i R)
        (modeCreate (rawJetMode G theta j R) (modeCreate (rawJetMode G theta k R) f)) := by
    simp only [modeCreate_apply,mul_assoc]
  rw [hc]
  simp only [ip]
  rw [mode_create_adjoint,mode_create_adjoint,mode_create_adjoint]

end TorusLean.Shared.BosonAnchoredTripleRows
