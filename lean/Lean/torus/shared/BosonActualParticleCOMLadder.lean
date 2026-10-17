import torus.shared.BosonNaturalWordSpan
import torus.shared.BosonFiniteCertificateNatCOMParticle

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonActualParticleCOMLadder
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.ParameterCellAdjoint
open TorusLean.Shared.BosonAnchoredNatLinearActions TorusLean.Shared.BosonAnchoredNatLadder
open TorusLean.Shared.BosonAnchoredNatRaiseIntertwining TorusLean.Shared.BosonAnchoredNatLowerIntertwining
open TorusLean.Shared.BosonNaturalWordSpan
open TorusLean.Shared.ParameterLadderScaling TorusLean.Shared.ParameterLadderIntegration
open scoped ContDiff

/-- Original cell ladder for every finite k-particle relative polynomial.
Particle number and true lowering vacuum suffice; no orbital-degree cutoff,
smoothness, boundary, or parameter-action premise is supplied. -/
theorem actualParticleCOM_isLadder (G : Geometry) (theta : Twist) (k : ℕ) [NeZero k]
    (q : Core (OrbitalIndex G theta) ℂ) (p : Core ℕ ℂ)
    (hp : p.IsHomogeneous k) (hL : canonicalCOMLowerNat p=0) :
    IsLadderFamily G theta k (scaledCOMLevels k (actualNatCOMLevels G theta q p)) := by
  have hm (n : ℕ) : ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] p) ∈ naturalWordSpan k := by
    induction n with
    | zero => exact homogeneous_mem_naturalWordSpan k p hp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact canonicalCOMRaiseNat_preserves_wordSpan k _ ih
  apply scaledCOMLevels_isLadder
  · intro n
    exact (seedDualNat_contDiff G theta k q _ (hm n)).of_le (by simp)
  · intro n
    exact seedDualNat_boundary G theta k q _ (hm n)
  · intro n R
    simpa only [actualNatCOMLevels,Function.iterate_succ_apply'] using
      seedDualNat_raise_intertwining G theta k q _ (hm n) R
  · funext R
    have he := seedDualNat_lower_intertwining G theta k q p (hm 0) R
    rw [hL,map_zero,Pi.zero_apply] at he
    have hs : (Real.sqrt (k:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k)))))
    simpa only [actualNatCOMLevels,Function.iterate_zero,Function.id_def,Pi.zero_apply] using
      (mul_eq_zero.mp he).resolve_left hs
  · intro n R
    have he := seedDualNat_lower_intertwining G theta k q _ (hm (n+1)) R
    rw [canonicalCOMNat_lower_iterate_particle k n p hp hL,map_smul] at he
    simpa only [actualNatCOMLevels,Pi.smul_apply,smul_eq_mul,Nat.cast_add,Nat.cast_one,mul_assoc] using he

end TorusLean.Shared.BosonActualParticleCOMLadder
