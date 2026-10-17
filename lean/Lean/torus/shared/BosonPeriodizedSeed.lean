import torus.shared.PlaneJetParameterContinuity
import torus.shared.PhysicalBosonLinearEquiv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonPeriodizedSeed
open TorusLean.Boson TorusLean.Boson.UnitaryTransport
open TorusLean.Shared.PlaneJetMembership TorusLean.Shared.PlaneJetParameterContinuity
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.PhysicalBosonMembership
open TorusLean.Shared.PhysicalNBodyCarrier
open scoped BigOperators

/-- Finite planar mode polynomials are sent to the actual periodized physical
jets. This substitution is not assumed isometric or bounded on all degrees. -/
def anchoredSeed (G : Geometry) (theta : Twist) (K : ℕ) (R : ℂ) :
    Core (Fin K) ℂ →ₐ[ℂ] Core (PhysicalBosonSector.OrbitalIndex G theta) ℂ :=
  MvPolynomial.aeval (fun j => modeLinear
    ((orbitalBasis G theta).repr (rawPlaneJet G theta j.val R)))

theorem anchoredSeed_X (G : Geometry) (theta : Twist) (K : ℕ) (R : ℂ) (j : Fin K) :
    anchoredSeed G theta K R (MvPolynomial.X j) =
      modeLinear ((orbitalBasis G theta).repr (rawPlaneJet G theta j.val R)) := by
  simp [anchoredSeed]

theorem anchoredSeed_sector (G : Geometry) (theta : Twist) (K N : ℕ) (R : ℂ)
    (p : Core (Fin K) ℂ) (hp : p.IsHomogeneous N) :
    (anchoredSeed G theta K R p).IsHomogeneous N := by
  simpa only [anchoredSeed, one_mul] using hp.aeval
    (fun j : Fin K => modeLinear ((orbitalBasis G theta).repr (rawPlaneJet G theta j.val R)))
    (fun j => modeLinear_sector _)

/-- The finite anchored seed lands in the independent full physical carrier. -/
def physicalAnchoredSeed (G : Geometry) (theta : Twist) (K N : ℕ) (R : ℂ)
    (p : Core (Fin K) ℂ) (hp : p.IsHomogeneous N) : PhysicalBosonCarrier G theta N :=
  sectorPhysical G theta N ⟨anchoredSeed G theta K R p, anchoredSeed_sector G theta K N R p hp⟩

theorem physicalAnchoredSeed_apply (G : Geometry) (theta : Twist) (K N : ℕ) (R : ℂ)
    (p : Core (Fin K) ℂ) (hp : p.IsHomogeneous N) :
    (physicalAnchoredSeed G theta K N R p hp).val =
      coreFunction G theta N (anchoredSeed G theta K R p) := rfl

private theorem continuous_coeff_mul {ι : Type*} [DecidableEq ι]
    (f g : ℂ → Core ι ℂ)
    (hf : ∀ n, Continuous (fun R => (f R).coeff n))
    (hg : ∀ n, Continuous (fun R => (g R).coeff n)) (n : ι →₀ ℕ) :
    Continuous (fun R => (f R * g R).coeff n) := by
  simp only [MvPolynomial.coeff_mul]
  apply continuous_finsetSum
  intro q hq
  exact (hf q.1).mul (hg q.2)

theorem anchoredSeed_X_coeff_continuous (G : Geometry) (theta : Twist) (K : ℕ)
    (j : Fin K) (n : PhysicalBosonSector.OrbitalIndex G theta →₀ ℕ) :
    Continuous (fun R : ℂ => (anchoredSeed G theta K R (MvPolynomial.X j)).coeff n) := by
  simp only [anchoredSeed_X, modeLinear, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul]
  apply continuous_finsetSum
  intro i hi
  exact ((PiLp.continuous_apply 2 (fun _ : PhysicalBosonSector.OrbitalIndex G theta => ℂ) i).comp (rawJetCoordinates_continuous G theta j.val)).mul continuous_const

/-- Every finite physical occupation coefficient is continuous at the true
anchor, by finite polynomial substitution, without an infinite-domain extension. -/
theorem anchoredSeed_coeff_continuous (G : Geometry) (theta : Twist) (K : ℕ)
    (p : Core (Fin K) ℂ) (n : PhysicalBosonSector.OrbitalIndex G theta →₀ ℕ) :
    Continuous (fun R : ℂ => (anchoredSeed G theta K R p).coeff n) := by
  induction p using MvPolynomial.induction_on generalizing n with
  | C c =>
    simp only [anchoredSeed, MvPolynomial.aeval_C]
    exact continuous_const
  | add p q hp hq =>
    simp only [map_add, MvPolynomial.coeff_add]
    exact (hp n).add (hq n)
  | mul_X p j hp =>
    simp only [map_mul]
    exact continuous_coeff_mul _ _ hp (anchoredSeed_X_coeff_continuous G theta K j) n

#print axioms anchoredSeed_X
#print axioms anchoredSeed_sector
#print axioms physicalAnchoredSeed_apply
#print axioms anchoredSeed_X_coeff_continuous
#print axioms anchoredSeed_coeff_continuous
end TorusLean.Shared.BosonPeriodizedSeed
