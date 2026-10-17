import torus.shared.PlaneJetParameterContinuity
import Mathlib.Analysis.Complex.TaylorSeries

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.CoherentJetExpansion
open TorusLean.Geometry TorusLean.Shared.GroundJetReproducing
open TorusLean.Shared.PlaneJetReproducing TorusLean.Shared.PlaneJetMembership
open TorusLean.Shared.PhysicalBosonSector
open scoped ComplexConjugate BigOperators

/-- The physical coefficient of T_R e_j in the displaced coherent seed.
The conjugated offset follows the conjugate-first Hilbert convention. -/
def coherentJetWeight (beta : ℂ) (j : ℕ) : ℂ :=
  gaussianFactor 1 beta * conj beta ^ j / (Real.sqrt (j.factorial:ℝ):ℂ)

private theorem sqrt_factorial_square (j : ℕ) :
    (Real.sqrt (j.factorial:ℝ):ℂ)^2 = (j.factorial:ℂ) := by
  exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg j.factorial)

/-- Entire Taylor convergence of the actual back-translated section's
canonical factor, with its original normalized derivative coefficient. -/
theorem rawJetCoefficient_taylor_hasSum (G : Geometry) (theta : Twist)
    (h : RawLLL G theta 1) (R beta : ℂ) :
    HasSum (fun j : ℕ => (beta^j / (Real.sqrt (j.factorial:ℝ):ℂ)) *
      rawJetCoefficient G theta h j R)
      (translatedStrippedFactor (-R) (canonicalRawStripped G theta h) beta) := by
  have ht := Complex.hasSum_taylorSeries_of_entire
    (translatedStrippedFactor_differentiable (-R) _ (canonicalRawStripped_differentiable G theta h))
    0 beta
  convert ht using 1
  ext j
  simp only [rawJetCoefficient, sub_zero, smul_eq_mul]
  rw [div_mul_div_comm, ← pow_two, sqrt_factorial_square]
  ring

private theorem gaussianFactor_conj (z : ℂ) :
    conj (gaussianFactor 1 z) = gaussianFactor 1 z := by
  rw [gaussianFactor_eq_norm, ← Complex.exp_conj, Complex.conj_ofReal]

/-- The actual magnetic phase from translating the anchor and the coherent
spectator offset. It is retained before taking any rank-one projector. -/
theorem conjugate_backTranslate (R beta : ℂ) (h : ℂ → ℂ) :
    conj (magneticTranslate 1 (-R) h beta) =
      magneticCocycle 1 R beta * conj (h (R+beta)) := by
  simp only [magneticTranslate, map_mul, ← Complex.exp_conj, sub_neg_eq_add]
  rw [add_comm beta R]
  congr 1
  unfold magneticCocycle magneticExponent
  congr 1
  simp only [map_div₀, map_mul, map_sub, map_neg, Complex.conj_conj,
    Complex.ofReal_one, one_mul, map_ofNat]
  ring

/-- Actual scalar Hilbert pairings of the coherent jet series converge;
no infinite periodization or Taylor interchange is assumed. -/
theorem coherentJet_inner_hasSum (G : Geometry) (theta : Twist)
    (h : LLL G theta 1) (R beta : ℂ) :
    HasSum (fun j : ℕ => coherentJetWeight beta j * inner ℂ h (rawPlaneJet G theta j R))
      (magneticCocycle 1 R beta * inner ℂ h (rawPlaneJet G theta 0 (R+beta))) := by
  have hs := (rawJetCoefficient_taylor_hasSum G theta h R beta).mul_left (gaussianFactor 1 beta)
  have hc := Complex.hasSum_conj'.mpr hs
  have hf := magneticTranslate_stripped_factor (-R) h.val (canonicalRawStripped G theta h)
    (canonicalRawStripped_factor G theta h) beta
  rw [← hf, conjugate_backTranslate] at hc
  convert hc using 1
  · ext j
    rw [← inner_conj_symm, rawPlaneJet_inner_reproduces]
    simp only [coherentJetWeight, map_mul, map_div₀, map_pow,
      gaussianFactor_conj, Complex.conj_ofReal]
    ring
  · rw [← inner_conj_symm, rawPlaneJet_inner_reproduces, rawJetCoefficient_zero]

/-- Strong Hilbert-space HasSum in the full actual LLL. The finite physical
ON basis upgrades all scalar Taylor identities to the original cell norm. -/
theorem coherentJet_hasSum (G : Geometry) (theta : Twist) (R beta : ℂ) :
    HasSum (fun j : ℕ => coherentJetWeight beta j • rawPlaneJet G theta j R)
      (magneticCocycle 1 R beta • rawPlaneJet G theta 0 (R+beta)) := by
  let b := orbitalBasis G theta
  have hs := hasSum_sum (s := (Finset.univ : Finset (OrbitalIndex G theta)))
    (fun i _ => (coherentJet_inner_hasSum G theta (b i) R beta).smul_const (b i))
  convert hs using 1
  · ext j
    conv_lhs => rw [← b.sum_repr (rawPlaneJet G theta j R)]
    simp only [Finset.smul_sum, smul_smul, OrthonormalBasis.repr_apply_apply]
  · conv_lhs => rw [← b.sum_repr (rawPlaneJet G theta 0 (R+beta))]
    simp only [Finset.smul_sum, smul_smul, OrthonormalBasis.repr_apply_apply]

/-- Absolute convergence follows in the finite-dimensional physical LLL;
it is not a claim that the infinite planar periodizer is bounded. -/
theorem coherentJet_summable_norm (G : Geometry) (theta : Twist) (R beta : ℂ) :
    Summable (fun j : ℕ => ‖coherentJetWeight beta j • rawPlaneJet G theta j R‖) :=
  (coherentJet_hasSum G theta R beta).summable.norm

#print axioms coherentJet_summable_norm
#print axioms rawJetCoefficient_taylor_hasSum
#print axioms conjugate_backTranslate
#print axioms coherentJet_inner_hasSum
#print axioms coherentJet_hasSum
end TorusLean.Shared.CoherentJetExpansion
