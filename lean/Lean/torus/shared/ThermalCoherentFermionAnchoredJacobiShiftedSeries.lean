import torus.shared.ThermalCoherentFermionAnchoredJacobiSpectatorGenerating
import torus.shared.BosonAnchoredScalarKernel
import torus.shared.ThermalCoherentAnchoredSeries

/-! Finite reindexings of the genuine scalar coherent expansions. These
absorb z and conj(z) into normalized coefficient sequences, so the already
proved absolute anchored L1 exchange applies unchanged. All shifts include
their zero boundary term. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiShiftedSeries
open MeasureTheory TorusLean.Geometry
open TorusLean.Shared.BosonAnchoredScalarExpansion TorusLean.Shared.BosonAnchoredScalarKernel
open TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiPairGenerating
open TorusLean.Shared.ThermalCoherentAnchoredSeries TorusLean.Shared.ThermalCoherentAnchoredMoments
open TorusLean.Shared.ChargeTwoScaling TorusLean.Shared.PhysicalFermionJetPair
open scoped BigOperators ComplexConjugate

def sqrtShift (A : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | j+1 => (Real.sqrt (j+1:ℝ):ℂ)*A j

def sqrtNext (A : ℕ → ℂ) (j : ℕ) : ℂ :=
  (Real.sqrt (j+1:ℝ):ℂ)*A (j+1)

def pairShift (B : ℕ → ℂ) (j : ℕ) : ℂ :=
  (Real.sqrt (2:ℝ):ℂ)⁻¹*sqrtShift B j

def degreeSequence (A : ℕ → ℂ) (j : ℕ) : ℂ := (j:ℂ)*A j

/-- The apparent shifted derivative is exactly the degree coefficient;
the j=0 boundary is literally zero. -/
theorem sqrtShift_sqrtNext (A : ℕ → ℂ) :
    sqrtShift (sqrtNext A)=degreeSequence A := by
  funext j
  cases j with
  | zero => simp [sqrtShift,degreeSequence]
  | succ j =>
    have hs : (Real.sqrt (j+1:ℝ):ℂ)^2=((j+1:ℕ):ℂ) := by
      exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤j+1 by positivity)
    simp only [sqrtShift,sqrtNext,degreeSequence]
    rw [← mul_assoc,← pow_two,hs]

private theorem sqrt_nat_add_one_le (j : ℕ) : Real.sqrt (j+1:ℝ)≤(j:ℝ)+1 :=
  Real.sqrt_le_self_iff.mpr (Or.inr (by
    have hj : (0:ℝ)≤j := Nat.cast_nonneg j
    linarith))

theorem polynomial_sqrtNext (A : ℕ → ℂ) (hA : HasPolynomialNormBound A) :
    HasPolynomialNormBound (sqrtNext A) := by
  obtain ⟨C,p,hA⟩ := hA
  have hC : 0≤C := (norm_nonneg (A 0)).trans (by simpa using hA 0)
  refine ⟨C*2^p,p+1,?_⟩
  intro j
  simp only [sqrtNext,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc
    _ ≤ ((j:ℝ)+1)*(C*((j:ℝ)+2)^p) := by
      apply mul_le_mul (sqrt_nat_add_one_le j)
        (by simpa only [Nat.cast_add,Nat.cast_one,add_assoc,
          show (1:ℝ)+1=2 by norm_num] using hA (j+1))
        (norm_nonneg _) (by positivity)
    _ ≤ ((j:ℝ)+1)*(C*(2*((j:ℝ)+1))^p) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hC
      apply pow_le_pow_left₀ (by positivity)
      have hj : 0≤(j:ℝ) := Nat.cast_nonneg j
      linarith
    _ = _ := by rw [mul_pow,pow_succ]; ring

theorem polynomial_sqrtShift (A : ℕ → ℂ) (hA : HasPolynomialNormBound A) :
    HasPolynomialNormBound (sqrtShift A) := by
  obtain ⟨C,p,hA⟩ := hA
  have hC : 0≤C := (norm_nonneg (A 0)).trans (by simpa using hA 0)
  refine ⟨C,p+1,?_⟩
  intro j
  cases j with
  | zero => simp [sqrtShift,hC]
  | succ j =>
    simp only [sqrtShift,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),Nat.cast_add,Nat.cast_one]
    calc
      _ ≤ ((j:ℝ)+1)*(C*((j:ℝ)+1)^p) :=
        mul_le_mul (sqrt_nat_add_one_le j) (hA j) (norm_nonneg _) (by positivity)
      _ = C*((j:ℝ)+1)^(p+1) := by rw [pow_succ]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hC
        apply pow_le_pow_left₀ (by positivity)
        linarith

theorem polynomial_mul_const_left (c : ℂ) (A : ℕ → ℂ)
    (hA : HasPolynomialNormBound A) : HasPolynomialNormBound (fun j => c*A j) := by
  obtain ⟨C,p,hA⟩ := hA
  refine ⟨‖c‖*C,p,?_⟩
  intro j
  simpa only [norm_mul,mul_assoc] using mul_le_mul_of_nonneg_left (hA j) (norm_nonneg c)

theorem polynomial_pairShift (B : ℕ → ℂ) (hB : HasPolynomialNormBound B) :
    HasPolynomialNormBound (pairShift B) :=
  polynomial_mul_const_left _ _ (polynomial_sqrtShift B hB)

theorem polynomial_degreeSequence (A : ℕ → ℂ) (hA : HasPolynomialNormBound A) :
    HasPolynomialNormBound (degreeSequence A) := by
  rw [← sqrtShift_sqrtNext]
  exact polynomial_sqrtShift _ (polynomial_sqrtNext A hA)

private theorem sqrt_factorial_succ (j : ℕ) :
    (Real.sqrt ((j+1).factorial:ℝ):ℂ) =
      (Real.sqrt (j+1:ℝ):ℂ)*(Real.sqrt (j.factorial:ℝ):ℂ) := by
  rw [Nat.factorial_succ,Nat.cast_mul,Real.sqrt_mul (by positivity),Complex.ofReal_mul]
  norm_num

private theorem primalWeight_shift (z : ℂ) (j : ℕ) :
    primalCoherentWeight z (j+1)*(Real.sqrt (j+1:ℝ):ℂ) = z*primalCoherentWeight z j := by
  unfold primalCoherentWeight
  rw [sqrt_factorial_succ,pow_succ]
  have h0 : (Real.sqrt (j.factorial:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have h1 : (Real.sqrt (j+1:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  field_simp <;> ring

private theorem pairWeight_shift (z : ℂ) (j : ℕ) :
    pairWeight z (j+1)*((Real.sqrt (2:ℝ):ℂ)⁻¹*(Real.sqrt (j+1:ℝ):ℂ)) =
      z*pairWeight z j := by
  unfold pairWeight
  rw [sqrt_factorial_succ,pow_succ]
  have h0 : (Real.sqrt (j.factorial:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have h1 : (Real.sqrt (j+1:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have h2 : (Real.sqrt (2:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  unfold scale
  field_simp <;> ring

/-- Reindex the actual coherent series, without losing its zero boundary. -/
theorem primal_hasSum_sqrtShift (A : ℕ → ℂ) (z a : ℂ)
    (hA : HasSum (fun j => primalCoherentWeight z j*A j) a) :
    HasSum (fun j => primalCoherentWeight z j*sqrtShift A j) (z*a) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.sum_range_one,sqrtShift,mul_zero,sub_zero]
  convert hA.mul_left z using 1
  ext j
  rw [← mul_assoc,primalWeight_shift]
  ring

/-- Original charge-two shift includes exactly one reciprocal sqrt2. -/
theorem pair_hasSum_pairShift (B : ℕ → ℂ) (z b : ℂ)
    (hB : HasSum (fun j => pairWeight z j*B j) b) :
    HasSum (fun j => pairWeight z j*pairShift B j) (z*b) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [Finset.sum_range_one,pairShift,sqrtShift,mul_zero,sub_zero]
  convert hB.mul_left z using 1
  ext j
  calc
    _ = (pairWeight z (j+1)*((Real.sqrt (2:ℝ):ℂ)⁻¹*
        (Real.sqrt (j+1:ℝ):ℂ)))*B j := by ring
    _ = _ := by rw [pairWeight_shift]; ring

/-- The fermionic pair generating weight is the same scalar Gaussian
normalization used by the accepted absolute anchored-series theorem. -/
theorem pairWeight_eq_anchoredWeight (z : ℂ) (p : ℕ) :
    pairWeight z p=pairCoherentWeight z p := by
  rw [pairWeight,pairCoherentWeight,← gaussian_one_mul_self]
  simp only [pow_two,mul_pow,scale]
  ring

/-- Genuine pointwise product expansion of two actual coherent HasSums.
All later use supplies the physical spectator and physical charge-two pair. -/
theorem scalar_kernel_hasSum (A B : ℕ → ℂ) (z a b : ℂ)
    (hA : HasSum (fun j => primalCoherentWeight z j*A j) a)
    (hB : HasSum (fun p => pairWeight z p*B p) b) :
    HasSum (fun jp : ℕ×ℕ => anchoredSeriesTerm A B jp z)
      (gaussianFactor 1 z*conj a*b) := by
  have ha := Complex.hasSum_conj'.mpr hA
  have ht := summable_mul_of_summable_norm ha.summable.norm hB.summable.norm
  have hs := (ha.mul hB ht).mul_left (gaussianFactor 1 z)
  convert hs using 1
  · ext jp
    simp only [anchoredSeriesTerm,map_mul,pairWeight_eq_anchoredWeight]
    rw [show gaussianFactor 1 z*(conj (primalCoherentWeight z jp.1)*conj (A jp.1)*
      (pairCoherentWeight z jp.2*B jp.2)) =
      (gaussianFactor 1 z*conj (primalCoherentWeight z jp.1)*pairCoherentWeight z jp.2)*
        conj (A jp.1)*B jp.2 by ring,anchored_weight_factor]
  · ring

end TorusLean.Shared.ThermalCoherentFermionAnchoredJacobiShiftedSeries
