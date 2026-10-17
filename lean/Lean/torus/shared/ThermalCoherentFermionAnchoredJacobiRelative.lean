import torus.shared.ThermalCoherentFermionAnchoredJacobiAlgebra

/-! Reconciliation of the actual normalized marked relative exterior image
with the original paperPauliCoefficient/formalRelativeSeed. The equality is
proved from finite factorial formulas; no normalized relative basis is assumed. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchored
open TorusLean.Fermion
open TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators

private def relativeUnsigned (d p : ℕ) : ℝ :=
  (d.choose p:ℝ)*(2:ℝ)^(d-p)*Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ))*
    Real.sqrt ((d-p).factorial:ℝ) / Real.sqrt ((6:ℝ)^d*(d.factorial:ℝ))

private theorem sqrt_power_square (x : ℝ) (hx : 0≤x) (n : ℕ) :
    ((Real.sqrt x)^n)^2=x^n := by
  rw [←pow_mul,Nat.mul_comm n 2,pow_mul,Real.sq_sqrt hx]

private theorem relativeUnsigned_sq (d p : ℕ) (hp : p≤d) :
    (relativeUnsigned d p)^2 =
      (d.choose p:ℝ)*(1/3:ℝ)^p*(2/3:ℝ)^(d-p) := by
  have hf : (d.choose p:ℝ)*(p.factorial:ℝ)*((d-p).factorial:ℝ)=(d.factorial:ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hp
  have hd : p+(d-p)=d := by omega
  have hpowers : ((2:ℝ)^(d-p))^2*(2:ℝ)^p =
      (6:ℝ)^d*(1/3:ℝ)^p*(2/3:ℝ)^(d-p) := by
    rw [←hd,show (6:ℝ)=2*3 by norm_num]
    simp only [Nat.add_sub_cancel_left,pow_add,mul_pow,div_pow,one_pow,pow_two]
    field_simp
    <;> ring
  have hnum : (d.choose p:ℝ)^2*((2:ℝ)^(d-p))^2*
      ((2:ℝ)^p*(p.factorial:ℝ))*((d-p).factorial:ℝ) =
      ((d.choose p:ℝ)*(1/3:ℝ)^p*(2/3:ℝ)^(d-p))*
        ((6:ℝ)^d*(d.factorial:ℝ)) := by
    calc
      _ = (d.choose p:ℝ)*
          ((d.choose p:ℝ)*(p.factorial:ℝ)*((d-p).factorial:ℝ))*
          (((2:ℝ)^(d-p))^2*(2:ℝ)^p) := by ring
      _ = _ := by rw [hf,hpowers]; ring
  have hden : (6:ℝ)^d*(d.factorial:ℝ)≠0 := by positivity
  unfold relativeUnsigned
  rw [div_pow,mul_pow,mul_pow,mul_pow,
    Real.sq_sqrt (by positivity),Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity),hnum]
  exact mul_div_cancel_right₀ _ hden

private theorem relativeUnsigned_eq (d p : ℕ) (hp : p≤d) :
    relativeUnsigned d p = Real.sqrt (d.choose p:ℝ)*
      (Real.sqrt (1/3:ℝ))^p*(Real.sqrt (2/3:ℝ))^(d-p) := by
  apply (sq_eq_sq₀ (by unfold relativeUnsigned; positivity) (by positivity)).mp
  rw [relativeUnsigned_sq d p hp,mul_pow,mul_pow,
    Real.sq_sqrt (by positivity),sqrt_power_square _ (by norm_num),
    sqrt_power_square _ (by norm_num)]

theorem fermionMarkedRelative_power (d : ℕ) :
    fermionMarkedRelative^d = ∑ p∈Finset.range (d+1),
      ((d.choose p:ℂ)*(-2:ℂ)^(d-p)) • (markedPair^p*markedSpectator^(d-p)) := by
  have hT : fermionMarkedRelative=markedPair+(-2:ℂ) • markedSpectator := by
    simp [fermionMarkedRelative,sub_eq_add_neg]
  rw [hT,add_pow]
  apply Finset.sum_congr rfl
  intro p hp
  simp only [smul_pow,MvPolynomial.smul_eq_C_mul,map_mul,map_pow,map_natCast]
  ring

theorem fermionRelativeCoefficient_normalization (d p : ℕ) (hp : p≤d) :
    (Real.sqrt ((6:ℝ)^d*(d.factorial:ℝ)):ℂ)⁻¹ *
      ((d.choose p:ℂ)*(-2:ℂ)^(d-p))*
      ((Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ)):ℂ)*
        (Real.sqrt ((d-p).factorial:ℝ):ℂ)) = (paperPauliCoefficient d p:ℂ) := by
  have he := congrArg (fun r : ℝ => (r:ℂ)) (relativeUnsigned_eq d p hp)
  simp only [relativeUnsigned,Complex.ofReal_div,Complex.ofReal_mul,
    Complex.ofReal_pow,Complex.ofReal_natCast,Complex.ofReal_ofNat] at he
  simp only [paperPauliCoefficient,Complex.ofReal_mul,Complex.ofReal_pow,
    Complex.ofReal_neg,Complex.ofReal_one]
  rw [show (-2:ℂ)=(-1:ℂ)*2 by norm_num,mul_pow]
  calc
    _ = (-1:ℂ)^(d-p)*
        (((d.choose p:ℂ)*(2:ℂ)^(d-p)*
          (Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ)):ℂ)*
          (Real.sqrt ((d-p).factorial:ℝ):ℂ)) /
          (Real.sqrt ((6:ℝ)^d*(d.factorial:ℝ)):ℂ)) := by ring
    _ = _ := by rw [he]; ring

/-- The finite marked relative source is the paper's original actual
exterior source, with (-1)^(d-p) and all factorials unchanged. -/
theorem formalJacobiColumn_relative (d : ℕ) :
    formalJacobiColumn 0 d=formalRelativeSeed d := by
  simp only [formalJacobiColumn,pow_zero,Nat.factorial_zero,Nat.cast_one,
    mul_one,Real.sqrt_one,Complex.ofReal_one,inv_one,one_mul]
  rw [fermionMarkedRelative_power,map_sum]
  simp only [Finset.smul_sum,map_smul,fermionMarkedW3_pair_spectator,
    fermionMarkedBasisInsertion,smul_smul,formalRelativeSeed]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  have hle : p≤d := by have := Finset.mem_range.mp hp; omega
  simpa only [mul_assoc] using fermionRelativeCoefficient_normalization d p hle

end TorusLean.Shared.ThermalCoherentFermionAnchored
