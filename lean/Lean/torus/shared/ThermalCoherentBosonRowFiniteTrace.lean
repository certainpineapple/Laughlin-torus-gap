import torus.shared.ThermalCoherentBosonRowRotation
import torus.shared.ThermalCoherentJacobiAlgebra

/-! Complete pair-COM/spectator finite trace after the actual W3 insertion.
Both sides contain every degree-t auxiliary state. The image vectors need
not be orthogonal, independent, normalized, or nonzero. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentBosonRowRotation
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Shared.ThermalCoherentJacobiFourParseval
open scoped BigOperators ComplexConjugate

/-- Canonical normalized pair oscillator uses A/sqrt(2); the spectator uses B. -/
def canonicalPairSpectatorMarked : Core (Fin 2) ℂ →ₐ[ℂ] MarkedOscillator :=
  MvPolynomial.aeval (fun i => if i=0 then
    (Real.sqrt (2:ℝ):ℂ)⁻¹ • MvPolynomial.X 0 else MvPolynomial.X 1)

def canonicalPairSpectatorW3 : Core (Fin 2) ℂ →ₗ[ℂ] Core ℕ ℂ :=
  markedW3.comp canonicalPairSpectatorMarked.toLinearMap

private theorem canonicalPairSpectatorMarked_X_zero :
    canonicalPairSpectatorMarked (MvPolynomial.X 0)=(Real.sqrt (2:ℝ):ℂ)⁻¹ • MvPolynomial.X 0 := by
  simp [canonicalPairSpectatorMarked]
private theorem canonicalPairSpectatorMarked_X_one :
    canonicalPairSpectatorMarked (MvPolynomial.X 1)=MvPolynomial.X 1 := by
  simp [canonicalPairSpectatorMarked]

private theorem chargeRoot_factorized (k n : ℕ) :
    (Real.sqrt ((k:ℝ)^n*(n.factorial:ℝ)):ℂ)=(Real.sqrt (k:ℝ):ℂ)^n*factorialRootNat n := by
  have hs (m : ℕ) : Real.sqrt ((k:ℝ)^m)=(Real.sqrt (k:ℝ))^m := by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ,Real.sqrt_mul (by positivity),ih,pow_succ]
  rw [Real.sqrt_mul (by positivity : (0:ℝ)≤(k:ℝ)^n),hs,Complex.ofReal_mul,Complex.ofReal_pow]
  rfl

/-- Unrotated normalized auxiliary basis is the genuine original pair/spectator source. -/
theorem canonicalPairSpectatorW3_word (p j : ℕ) :
    canonicalPairSpectatorW3 (normalizedSpectatorWord p j)=pairCOMSeed p*MvPolynomial.X j := by
  change markedW3 (canonicalPairSpectatorMarked (normalizedSpectatorWord p j))=_
  simp only [normalizedSpectatorWord,map_smul,map_mul,map_pow,
    canonicalPairSpectatorMarked_X_zero,canonicalPairSpectatorMarked_X_one,smul_pow,smul_mul_assoc]
  rw [smul_smul]
  have he : (factorialRootNat p*factorialRootNat j)⁻¹*(Real.sqrt (2:ℝ):ℂ)⁻¹^p =
      (Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ)):ℂ)⁻¹*(factorialRootNat j)⁻¹ := by
    have hf := chargeRoot_factorized 2 p
    norm_num only [Nat.cast_ofNat] at hf
    rw [hf]
    simp only [mul_inv,inv_pow]
    ring
  rw [he]
  simpa only [map_smul] using markedW3_normalized_pair_spectator p j

/-- The first rotated normalized coordinate is the true total COM direction. -/
theorem canonicalPairSpectatorMarked_rotated_zero :
    canonicalPairSpectatorMarked (rotatePairSpectator (MvPolynomial.X 0)) =
      (Real.sqrt (3:ℝ):ℂ)⁻¹ • markedCOM := by
  rw [rotatePairSpectator_X_zero,map_add,map_smul,map_smul,
    canonicalPairSpectatorMarked_X_zero,canonicalPairSpectatorMarked_X_one,smul_smul]
  have h2 : (Real.sqrt (2:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have he : ((Real.sqrt (2:ℝ):ℂ)/(Real.sqrt (3:ℝ):ℂ))*(Real.sqrt (2:ℝ):ℂ)⁻¹ =
      (Real.sqrt (3:ℝ):ℂ)⁻¹ := by field_simp
  rw [he,markedCOM,smul_add]

/-- The second direction is the paper's actual -A+2B relative oscillator. -/
theorem canonicalPairSpectatorMarked_rotated_one :
    canonicalPairSpectatorMarked (rotatePairSpectator (MvPolynomial.X 1)) =
      (Real.sqrt (6:ℝ):ℂ)⁻¹ • markedRelative := by
  rw [rotatePairSpectator_X_one,map_add,map_smul,map_smul,
    canonicalPairSpectatorMarked_X_zero,canonicalPairSpectatorMarked_X_one,smul_smul]
  have hs : (Real.sqrt (6:ℝ):ℂ)=(Real.sqrt (2:ℝ):ℂ)*(Real.sqrt (3:ℝ):ℂ) := by
    rw [show (6:ℝ)=2*3 by norm_num,Real.sqrt_mul (by norm_num),Complex.ofReal_mul]
  have h2 : (Real.sqrt (2:ℝ):ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hn2 : (Real.sqrt (2:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have hn3 : (Real.sqrt (3:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  rw [markedRelative,smul_add,smul_neg,smul_smul,hs]
  have he : (Real.sqrt (2:ℝ):ℂ)/(Real.sqrt (3:ℝ):ℂ) =
      ((Real.sqrt (2:ℝ):ℂ)*(Real.sqrt (3:ℝ):ℂ))⁻¹*2 := by
    field_simp
    exact h2
  rw [he]
  simp only [mul_inv,neg_smul,neg_mul]
  module

private theorem raiseIterate_smul (n : ℕ) (c : ℂ) (p : Core ℕ ℂ) :
    (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] (c • p)=
      c • (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] p := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,map_smul,Function.iterate_succ_apply']

/-- The actual full marked insertion of the normalized rotated basis. -/
theorem canonicalPairSpectatorW3_rotated_word (n d : ℕ) :
    canonicalPairSpectatorW3 (rotatePairSpectator (normalizedSpectatorWord n d)) =
      normalizedCOMDescendant n (w3RelativeSeed d) := by
  change markedW3 (canonicalPairSpectatorMarked
    (rotatePairSpectator (normalizedSpectatorWord n d)))=_
  simp only [normalizedSpectatorWord,map_smul,map_mul,map_pow,
    canonicalPairSpectatorMarked_rotated_zero,canonicalPairSpectatorMarked_rotated_one,
    smul_pow,smul_mul_smul_comm]
  rw [smul_smul,markedW3_COM_power,
    normalizedCOMDescendant,w3RelativeSeed,raiseIterate_smul]
  have h3 := chargeRoot_factorized 3 n
  have h6 := chargeRoot_factorized 6 d
  norm_num only [Nat.cast_ofNat] at h3 h6
  rw [h3,h6]
  simp only [smul_smul,mul_inv,inv_pow]
  congr 1
  ring

/-- Complete finite degree-t pair/spectator cross trace, before any cell integral. -/
theorem w3_complete_auxiliary_cross (t : ℕ) (F G : Core ℕ ℂ →ₗ[ℂ] ℂ) :
    ∑ p : Fin (t+1), star (F (pairCOMSeed p.val*MvPolynomial.X (t-p.val)))*
      G (pairCOMSeed p.val*MvPolynomial.X (t-p.val)) =
    ∑ n : Fin (t+1), star (F (normalizedCOMDescendant n.val (w3RelativeSeed (t-n.val))))*
      G (normalizedCOMDescendant n.val (w3RelativeSeed (t-n.val))) := by
  have h := pairSpectatorRotation_ordered_cross t (F.comp canonicalPairSpectatorW3)
    (G.comp canonicalPairSpectatorW3)
  simpa only [LinearMap.comp_apply,canonicalPairSpectatorW3_word,
    canonicalPairSpectatorW3_rotated_word] using h.symm

end TorusLean.Shared.ThermalCoherentBosonRowRotation
