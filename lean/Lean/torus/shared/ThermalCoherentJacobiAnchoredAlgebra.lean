import torus.shared.ThermalCoherentJacobiAlgebra
import torus.shared.ThermalCoherentJacobiAnchoredWeights

/-! The second actual column of the anchored W3 kernel. The pair coordinate
is expanded in the marked source before symmetric insertion; no inverse of W3
or orthonormality of its relative images is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.ThermalCoherentJacobiAnchored
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Shared.ThermalCoherentJacobiWeights
open scoped BigOperators

/-- The original normalized pair COM level with the spectator in its ground. -/
def pairAnchoredSeed (l : ℕ) : Core ℕ ℂ := pairCOMSeed l * MvPolynomial.X 0

theorem markedPair_eq : (MvPolynomial.X 0 : MarkedOscillator) =
    (3:ℂ)⁻¹ • (-markedRelative+(2:ℂ) • markedCOM) := by
  simp only [markedRelative,markedCOM]
  module

theorem markedPair_power (l : ℕ) :
    (MvPolynomial.X 0 : MarkedOscillator)^l = (3:ℂ)⁻¹^l •
      ∑ d ∈ Finset.range (l+1), ((l.choose d:ℂ)*(-1:ℂ)^d*(2:ℂ)^(l-d)) •
        (markedCOM^(l-d)*markedRelative^d) := by
  rw [markedPair_eq,smul_pow,add_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [neg_pow]
  simp only [smul_pow,MvPolynomial.smul_eq_C_mul,map_mul,map_natCast,
    map_neg,map_pow,map_ofNat,map_one]
  ring

theorem pairAnchoredSeed_eq_marked (l : ℕ) :
    pairAnchoredSeed l=(Real.sqrt ((2:ℝ)^l*(l.factorial:ℝ)):ℂ)⁻¹ •
      markedW3 ((MvPolynomial.X 0)^l) := by
  have h := markedW3_normalized_pair_spectator l 0
  simpa only [factorialRootNat,Nat.factorial_zero,Nat.cast_one,Real.sqrt_one,
    Complex.ofReal_one,inv_one,mul_one,pow_zero,map_smul,pairAnchoredSeed] using h.symm

theorem pairAnchoredSeed_bihomogeneous (l : ℕ) :
    (pairAnchoredSeed l).IsHomogeneous 3 ∧ (pairAnchoredSeed l).IsWeightedHomogeneous id l := by
  apply threeWordDegreeSpanNat_bihomogeneous l
  rw [pairAnchoredSeed_eq_marked]
  apply Submodule.smul_mem
  exact markedW3_homogeneous_mem l _ (MvPolynomial.isHomogeneous_X_pow 0 l)

private theorem pairChargeRoot_factorized (l : ℕ) :
    (Real.sqrt ((2:ℝ)^l*(l.factorial:ℝ)):ℂ) =
      (Real.sqrt (2:ℝ):ℂ)^l*factorialRootNat l := by
  have hs (k : ℕ) : Real.sqrt ((2:ℝ)^k)=(Real.sqrt (2:ℝ))^k := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ,Real.sqrt_mul (by positivity),ih,pow_succ]
  rw [Real.sqrt_mul (by positivity : (0:ℝ)≤2^l),hs,Complex.ofReal_mul,Complex.ofReal_pow]
  rfl

private theorem pairAnchored_normalization (l d : ℕ) (hd : d≤l) :
    (pairAnchoredJacobiAmplitude (l-d) d:ℂ) *
      (Real.sqrt ((3:ℝ)^(l-d)*((l-d).factorial:ℝ)):ℂ)⁻¹ *
      (Real.sqrt ((6:ℝ)^d*(d.factorial:ℝ)):ℂ)⁻¹ =
        (Real.sqrt ((2:ℝ)^l*(l.factorial:ℝ)):ℂ)⁻¹ *
          (3:ℂ)⁻¹^l*(l.choose d:ℂ)*(-1:ℂ)^d*(2:ℂ)^(l-d) := by
  have h3 : (Real.sqrt ((3:ℝ)^(l-d)*((l-d).factorial:ℝ)):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  have h6 : (Real.sqrt ((6:ℝ)^d*(d.factorial:ℝ)):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  have h2 : (Real.sqrt (2:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hl := factorialRootNat_ne_zero l
  rw [pairChargeRoot_factorized]
  simp only [pairAnchoredJacobiAmplitude,jacobiAmplitude,Nat.sub_add_cancel hd,
    Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_neg,
    Complex.ofReal_one,Complex.ofReal_ofNat,Complex.ofReal_natCast,factorialRootNat,inv_pow]
  simp only [factorialRootNat] at hl
  field_simp [h3,h6,h2,hl]

private theorem anchoredRaise_smul (n : ℕ) (c : ℂ) (p : Core ℕ ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] (c • p)=
      c • (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] p := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,map_smul,Function.iterate_succ_apply']

/-- Genuine second-column finite Jacobi identity, including its relative sign
and the original pair-root normalization. All descendants are the old Nat R. -/
theorem pairAnchoredSeed_jacobi_decomposition (l : ℕ) :
    pairAnchoredSeed l=∑ d ∈ Finset.range (l+1), (pairAnchoredJacobiAmplitude (l-d) d:ℂ) •
      normalizedCOMDescendant (l-d) (w3RelativeSeed d) := by
  rw [pairAnchoredSeed_eq_marked,markedPair_power,map_smul,map_sum]
  simp only [Finset.smul_sum,map_smul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [markedW3_COM_power,normalizedCOMDescendant,w3RelativeSeed,anchoredRaise_smul]
  simp only [smul_smul]
  congr 1
  simpa only [mul_assoc] using
    (pairAnchored_normalization l d (Nat.le_of_lt_succ (Finset.mem_range.mp hd))).symm

end TorusLean.Shared.ThermalCoherentJacobiAnchored
