import torus.shared.ThermalCoherentFermionAnchoredJacobiRelative
import torus.shared.FermionPairLowerExterior

/-! The marked differential lowering is transferred through the genuine
ordered-word exterior realization. The paper relative source's vacuum equality
is then a theorem, not a parameter-ladder premise or an independence assumption. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchored
open TorusLean.Fermion
open TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.ThermalCoherentFermionCOMWords
open scoped BigOperators

private def pairScale (p : ℕ) : ℝ := Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ))
private def singleScale (j : ℕ) : ℝ := Real.sqrt (j.factorial:ℝ)

private theorem pairScale_succ (p : ℕ) :
    pairScale (p+1)=Real.sqrt (2*(p+1:ℝ))*pairScale p := by
  unfold pairScale
  rw [show (2:ℝ)^(p+1)*((p+1).factorial:ℝ)=
    (2*(p+1:ℝ))*((2:ℝ)^p*(p.factorial:ℝ)) by
      simp only [pow_succ,Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
      ring]
  rw [Real.sqrt_mul (by positivity)]

private theorem singleScale_succ (j : ℕ) :
    singleScale (j+1)=Real.sqrt (j+1:ℝ)*singleScale j := by
  unfold singleScale
  rw [Nat.factorial_succ,Nat.cast_mul,Real.sqrt_mul (by positivity)]
  norm_cast

private theorem pairScale_lower (p : ℕ) :
    pairScale p*Real.sqrt (2*(p:ℝ))=2*(p:ℝ)*pairScale (p-1) := by
  cases p with
  | zero => simp
  | succ p =>
    simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
    rw [pairScale_succ]
    calc
      _ = (Real.sqrt (2*(p+1:ℝ)))^2*pairScale p := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity)]

private theorem singleScale_lower (j : ℕ) :
    singleScale j*Real.sqrt (j:ℝ)=(j:ℝ)*singleScale (j-1) := by
  cases j with
  | zero => simp
  | succ j =>
    simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
    rw [singleScale_succ]
    calc
      _ = (Real.sqrt (j+1:ℝ))^2*singleScale j := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity)]

private theorem realize_lower_three (p j : ℕ) :
    realize 3 (wordLower 3 (threeCoefficients p j)) =
      (Real.sqrt (2*(p:ℝ)):ℂ) • formalThreeSeed (p-1) j +
      (Real.sqrt (j:ℝ):ℂ) • formalThreeSeed p (j-1) := by
  cases p with
  | zero =>
    rw [realize_lower_three_pair_split,loweredPair_zero,zero_mul,zero_add]
    simp
  | succ p => simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
      using realize_lower_three_succ p j

def fermionMarkedWordBasis (p j : ℕ) : WordCoefficients 3 :=
  ((pairScale p:ℂ)*(singleScale j:ℂ)) • threeCoefficients p j

def fermionMarkedWords : FermionMarkedOscillator →ₗ[ℂ] WordCoefficients 3 :=
  (Finsupp.linearCombination ℂ (fun n : Fin 2 →₀ ℕ =>
    fermionMarkedWordBasis (n 0) (n 1))).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

theorem fermionMarkedWords_monomial (n : Fin 2 →₀ ℕ) (c : ℂ) :
    fermionMarkedWords (MvPolynomial.monomial n c)=
      c • fermionMarkedWordBasis (n 0) (n 1) := by
  change Finsupp.linearCombination ℂ
    (fun m : Fin 2 →₀ ℕ => fermionMarkedWordBasis (m 0) (m 1))
      (Finsupp.single n c)=_
  simp only [Finsupp.linearCombination_single]

theorem fermionMarkedWords_pair_spectator (p j : ℕ) :
    fermionMarkedWords (markedPair^p*markedSpectator^j)=fermionMarkedWordBasis p j := by
  simp only [markedPair,markedSpectator,MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul_monomial,mul_one,fermionMarkedWords_monomial,
    Finsupp.add_apply,Finsupp.single_apply]
  norm_num

theorem realize_fermionMarkedWords (f : FermionMarkedOscillator) :
    realize 3 (fermionMarkedWords f)=fermionMarkedW3 f := by
  induction f using MvPolynomial.induction_on' with
  | monomial n c =>
    simp only [fermionMarkedWords_monomial,fermionMarkedW3_monomial,
      fermionMarkedWordBasis,map_smul,realize_threeCoefficients,
      fermionMarkedBasisInsertion,pairScale,singleScale]
  | add f g hf hg => simp only [map_add,hf,hg]

private theorem realize_lower_markedBasis (p j : ℕ) :
    realize 3 (wordLower 3 (fermionMarkedWordBasis p j)) =
      (2*(p:ℂ)) • fermionMarkedBasisInsertion (p-1) j +
      (j:ℂ) • fermionMarkedBasisInsertion p (j-1) := by
  have hp := congrArg (fun r : ℝ => (r:ℂ)) (pairScale_lower p)
  have hj := congrArg (fun r : ℝ => (r:ℂ)) (singleScale_lower j)
  simp only [Complex.ofReal_mul,Complex.ofReal_natCast,Complex.ofReal_ofNat] at hp hj
  simp only [fermionMarkedWordBasis,map_smul,realize_lower_three,smul_add,smul_smul,
    fermionMarkedBasisInsertion]
  congr 1
  · congr 1
    calc
      _ = ((pairScale p:ℂ)*(Real.sqrt (2*(p:ℝ)):ℂ))*(singleScale j:ℂ) := by ring
      _ = _ := by rw [hp]; simp only [pairScale,singleScale]; ring
  · congr 1
    calc
      _ = (pairScale p:ℂ)*((singleScale j:ℂ)*(Real.sqrt (j:ℝ):ℂ)) := by ring
      _ = _ := by rw [hj]; simp only [pairScale,singleScale]; ring

/-- Genuine exterior lowering intertwined with the charge-weighted marked
pderiv, proved on the actual normalized pair/spectator monomials. -/
theorem realize_lower_fermionMarkedWords (f : FermionMarkedOscillator) :
    realize 3 (wordLower 3 (fermionMarkedWords f)) =
      fermionMarkedW3 ((2:ℂ) • MvPolynomial.pderiv 0 f + MvPolynomial.pderiv 1 f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [fermionMarkedWords_monomial,map_smul,map_smul,realize_lower_markedBasis]
    simp only [MvPolynomial.pderiv_monomial,map_add,map_smul,fermionMarkedW3_monomial,
      Finsupp.sub_apply,Finsupp.single_apply,smul_add,smul_smul]
    norm_num
    module
  | add f g hf hg =>
    simp only [map_add,smul_add,hf,hg]
    module

/-- Equality of finite word coefficients, stronger than equality of images. -/
theorem relativeCoefficients_eq_markedWords (d : ℕ) :
    relativeCoefficients d=(Real.sqrt ((6:ℝ)^d*(d.factorial:ℝ)):ℂ)⁻¹ •
      fermionMarkedWords (fermionMarkedRelative^d) := by
  rw [fermionMarkedRelative_power,map_sum]
  simp only [Finset.smul_sum,map_smul,fermionMarkedWords_pair_spectator,
    fermionMarkedWordBasis,pairScale,singleScale,smul_smul,relativeCoefficients]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  have hle : p≤d := by have := Finset.mem_range.mp hp; omega
  simpa only [mul_assoc] using (fermionRelativeCoefficient_normalization d p hle).symm

/-- The original paper relative source is a true exterior COM vacuum. -/
theorem relativeCoefficients_isExteriorVacuum (d : ℕ) :
    IsExteriorVacuum 3 (relativeCoefficients d) := by
  change realize 3 (wordLower 3 (relativeCoefficients d))=0
  rw [relativeCoefficients_eq_markedWords,map_smul,map_smul,
    realize_lower_fermionMarkedWords,fermionMarkedRelative_lower_power,map_zero,smul_zero]

end TorusLean.Shared.ThermalCoherentFermionAnchored
