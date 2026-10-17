import torus.shared.BosonActualParticleCOMLadder
import torus.shared.BosonPeriodizedSeedNat

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonNormalizedNatSeeds
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.BosonPeriodizedSeedNat
open TorusLean.Shared.BosonNaturalWordSpan TorusLean.Shared.BosonAnchoredNatRaiseIntertwining
open TorusLean.Shared.BosonAnchoredNatLinearActions TorusLean.Shared.BosonAnchoredNatLadder
open TorusLean.Shared.BosonActualParticleCOMLadder
open TorusLean.Shared.ParameterLadderScaling TorusLean.Shared.ParameterLadderIntegration

def normalizedNatSeed (k n : ℕ) (p : Core ℕ ℂ) : Core ℕ ℂ :=
  (Real.sqrt ((k:ℝ)^n * (n.factorial:ℝ)) : ℂ)⁻¹ •
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] p

theorem normalizedNatSeed_scale (k n : ℕ) :
    (Real.sqrt ((k:ℝ)^n * (n.factorial:ℝ)) : ℂ)⁻¹ =
      (Real.sqrt (n.factorial:ℝ):ℂ)⁻¹ * ((Real.sqrt (k:ℝ):ℂ)⁻¹)^n := by
  have hp : Real.sqrt ((k:ℝ)^n) = (Real.sqrt (k:ℝ))^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ,Real.sqrt_mul (pow_nonneg (Nat.cast_nonneg k) n),ih,pow_succ]
  rw [Real.sqrt_mul (pow_nonneg (Nat.cast_nonneg k) n),hp]
  push_cast
  simp only [mul_inv_rev,inv_pow]

theorem normalizedNatSeed_sector (k n : ℕ) (p : Core ℕ ℂ) (hp : p.IsHomogeneous k) :
    (normalizedNatSeed k n p).IsHomogeneous k := by
  have hm : ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] p) ∈ naturalWordSpan k := by
    induction n with
    | zero => exact homogeneous_mem_naturalWordSpan k p hp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact canonicalCOMRaiseNat_preserves_wordSpan k _ ih
  exact (MvPolynomial.homogeneousSubmodule ℕ ℂ k).smul_mem _
    (naturalWordSpan_homogeneous k _ hm)

theorem seedDualMapNat_normalized (G : Geometry) (theta : Twist) (k n : ℕ)
    (q : Core (OrbitalIndex G theta) ℂ) (p : Core ℕ ℂ) :
    seedDualMapNat G theta q (normalizedNatSeed k n p) =
      normalizedLevel (scaledCOMLevels k (actualNatCOMLevels G theta q p)) n := by
  simp only [normalizedNatSeed,map_smul,normalizedNatSeed_scale,normalizedLevel,
    scaledCOMLevels,smul_smul,actualNatCOMLevels]

theorem normalizedNatSeed_zero (k : ℕ) (p : Core ℕ ℂ) : normalizedNatSeed k 0 p=p := by
  simp [normalizedNatSeed]

/-- The true original anchored polynomial, rather than a redefined parameter
function, satisfies the full COM cross-inner identity. -/
theorem anchored_normalizedNatSeed_mu2 (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (q t : Core (OrbitalIndex G theta) ℂ) (p r : Core ℕ ℂ)
    (hp : p.IsHomogeneous k) (hr : r.IsHomogeneous k)
    (hpL : canonicalCOMLowerNat p=0) (hrL : canonicalCOMLowerNat r=0) (n m : ℕ) :
    cellInner G 2 (seedDualMapNat G theta q (normalizedNatSeed k n p))
      (seedDualMapNat G theta t (normalizedNatSeed k m r)) =
      if n=m then ((2/(k:ℝ):ℝ):ℂ) *
        cellInner G k (seedDualMapNat G theta q p) (seedDualMapNat G theta t r) else 0 := by
  rw [seedDualMapNat_normalized,seedDualMapNat_normalized]
  have he := normalized_ladder_mu2 G theta k _ _
    (actualParticleCOM_isLadder G theta k q p hp hpL)
    (actualParticleCOM_isLadder G theta k t r hr hrL) n m
  simpa only [scaledCOMLevels,pow_zero,one_smul,actualNatCOMLevels,
    Function.iterate_zero,Function.id_def] using he

end TorusLean.Shared.BosonNormalizedNatSeeds
