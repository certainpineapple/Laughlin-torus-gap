import torus.shared.BosonAnchoredNatLowerIntertwining
import torus.shared.ParameterLadderUnboundedScaling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace TorusLean.Shared.BosonAnchoredNatLadder
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.PhysicalBosonSector TorusLean.Shared.ParameterCellAdjoint
open TorusLean.Shared.BosonAnchoredNatLinearActions
open TorusLean.Shared.ThermalCoherentSeedWord
open TorusLean.Shared.BosonAnchoredNatRaiseIntertwining
open TorusLean.Shared.BosonAnchoredNatLowerIntertwining
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.ParameterLadderScaling TorusLean.Shared.ParameterLadderIntegration
open scoped ContDiff BigOperators

theorem wordPolynomial_mem_naturalWordSpan (s : List ℕ) :
    (wordPolynomial s : Core ℕ ℂ) ∈ naturalWordSpan s.length := by
  have he : (wordPolynomial s : Core ℕ ℂ) = canonicalWord s.length s.get := by
    conv_lhs => rw [← List.ofFn_get s]
    simp only [wordPolynomial, List.map_ofFn, List.prod_ofFn, canonicalWord, Function.comp_def]
  rw [he]
  exact Submodule.subset_span ⟨s.get, rfl⟩

theorem threeWordDegreeSpanNat_le (d : ℕ) : threeWordDegreeSpanNat d ≤ naturalWordSpan 3 := by
  apply Submodule.span_le.mpr
  rintro p ⟨s,hlen,hsum,rfl⟩
  rw [scaledWord]
  apply Submodule.smul_mem
  simpa only [hlen] using wordPolynomial_mem_naturalWordSpan s

theorem homogeneous_three_mem_naturalWordSpan (d : ℕ) (p : Core ℕ ℂ)
    (hN : p.IsHomogeneous 3) (hd : p.IsWeightedHomogeneous id d) :
    p ∈ naturalWordSpan 3 :=
  threeWordDegreeSpanNat_le d (homogeneous_mem_threeWordDegreeSpanNat d p hN hd)

def actualNatCOMLevels (G : Geometry) (theta : Twist)
    (q : Core (OrbitalIndex G theta) ℂ) (p : Core ℕ ℂ) (n : ℕ) : ℂ → ℂ :=
  seedDualMapNat G theta q ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] p)

/-- The only seed premises are true algebraic particle/degree membership and
relative vacuum. Every analytic domain and parameter-ladder field is proved. -/
theorem actualNatCOMLevels_isLadder (G : Geometry) (theta : Twist)
    (q : Core (OrbitalIndex G theta) ℂ) (d : ℕ) (p : Core ℕ ℂ)
    (hN : p.IsHomogeneous 3) (hd : p.IsWeightedHomogeneous id d)
    (hL : canonicalCOMLowerNat p = 0) :
    IsLadderFamily G theta 3 (scaledCOMLevels 3 (actualNatCOMLevels G theta q p)) := by
  have hm (n : ℕ) : ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] p) ∈ naturalWordSpan 3 := by
    have hh := canonicalCOMRaiseNat_iterate_bihomogeneous d n p hN hd
    exact homogeneous_three_mem_naturalWordSpan (d+n) _ hh.1 hh.2
  apply scaledCOMLevels_isLadder
  · intro n
    exact (seedDualNat_contDiff G theta 3 q _ (hm n)).of_le (by simp)
  · intro n
    exact seedDualNat_boundary G theta 3 q _ (hm n)
  · intro n R
    change (Real.sqrt (3:ℝ):ℂ)*parameterRaise 3 (seedDualMapNat G theta q _) R = _
    simpa only [Nat.cast_ofNat, actualNatCOMLevels, Function.iterate_succ_apply'] using
      seedDualNat_raise_intertwining G theta 3 q _ (hm n) R
  · funext R
    have he := seedDualNat_lower_intertwining G theta 3 q p
      (homogeneous_three_mem_naturalWordSpan d p hN hd) R
    rw [hL,map_zero,Pi.zero_apply] at he
    have hs : (Real.sqrt ((3:ℕ):ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))
    simpa only [actualNatCOMLevels,Function.iterate_zero,Function.id_def,Pi.zero_apply] using
      (mul_eq_zero.mp he).resolve_left hs
  · intro n R
    change (Real.sqrt (3:ℝ):ℂ)*parameterLower 3 (seedDualMapNat G theta q _) R = _
    have he := seedDualNat_lower_intertwining G theta 3 q _ (hm (n+1)) R
    rw [canonicalCOMNat_lower_iterate d n p hN hd hL,map_smul] at he
    simpa only [Nat.cast_ofNat,actualNatCOMLevels,Pi.smul_apply,smul_eq_mul,
      Nat.cast_add,Nat.cast_one,mul_assoc] using he

end TorusLean.Shared.BosonAnchoredNatLadder
