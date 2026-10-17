import torus.shared.FermionLocalJetFourCouplingTargetCoefficients

/-! The first relative spectator row is precisely the original normalized
antisymmetric pair coefficient, including its negative j<k sign. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.FermionRelativeFrame TorusLean.Shared.RelativeJetMap
open scoped BigOperators ComplexConjugate

private theorem sumPower_coeff (n j k : ℕ) :
    (((MvPolynomial.X 0+MvPolynomial.X 1 : Core (Fin 2) ℂ)^n).coeff (twoExponent j k)) =
      if j+k=n then (n.choose j : ℂ) else 0 := by
  simp [MvPolynomial.coeff_add_pow,twoExponent]

private theorem exponent_sub_zero (j k : ℕ) :
    twoExponent j k - Finsupp.single 0 1 = twoExponent (j-1) k := by
  ext i
  fin_cases i <;> simp [twoExponent]

private theorem exponent_sub_one (j k : ℕ) :
    twoExponent j k - Finsupp.single 1 1 = twoExponent j (k-1) := by
  ext i
  fin_cases i <;> simp [twoExponent]

/-- Exact signed factorial coefficient, including both zero-index boundaries. -/
theorem difference_sum_power_coeff (p j k : ℕ) (hjk : j+k=p+1) :
    (((MvPolynomial.X 0-MvPolynomial.X 1) *
      (MvPolynomial.X 0+MvPolynomial.X 1)^p : Core (Fin 2) ℂ).coeff (twoExponent j k)) =
      ((j:ℂ)-(k:ℂ)) * (p.factorial:ℂ) / ((j.factorial:ℂ)*(k.factorial:ℂ)) := by
  classical
  have hfac (n : ℕ) : (n.factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have h0 : (0 : Fin 2) ∈ (twoExponent j k).support ↔ j≠0 := by simp [twoExponent]
  have h1 : (1 : Fin 2) ∈ (twoExponent j k).support ↔ k≠0 := by simp [twoExponent]
  rw [sub_mul,AddMonoidAlgebra.coeff_sub,Finsupp.sub_apply,MvPolynomial.coeff_X_mul',
    MvPolynomial.coeff_X_mul']
  simp only [h0,h1,exponent_sub_zero,exponent_sub_one,sumPower_coeff]
  cases j with
  | zero =>
    cases k with
    | zero => omega
    | succ k =>
      have hp : p=k := by omega
      subst p
      simp only [Nat.zero_add,Nat.succ_sub_one,Nat.succ_ne_zero,not_false_eq_true,
        ne_eq,not_true_eq_false,if_false,if_true,Nat.choose_zero_right,Nat.factorial_zero,
        Nat.factorial_succ,Nat.cast_zero,Nat.cast_one,Nat.cast_add,Nat.cast_succ,Nat.cast_mul,one_mul,zero_sub]
      have hk : (k+1:ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero k
      field_simp [hk,hfac] <;> ring
  | succ j =>
    cases k with
    | zero =>
      have hp : p=j := by omega
      subst p
      simp only [Nat.add_zero,Nat.succ_sub_one,Nat.succ_ne_zero,not_false_eq_true,
        ne_eq,not_true_eq_false,if_false,if_true,Nat.choose_self,Nat.factorial_zero,
        Nat.factorial_succ,Nat.cast_zero,Nat.cast_one,Nat.cast_add,Nat.cast_succ,Nat.cast_mul,mul_one,sub_zero]
      have hj : (j+1:ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero j
      field_simp [hj,hfac] <;> ring
    | succ k =>
      have hp : p=j+k+1 := by omega
      have hleft : j+(k+1)=p := by omega
      have hright : (j+1)+k=p := by omega
      simp only [Nat.succ_sub_one,Nat.succ_ne_zero,ne_eq,not_false_eq_true,
        hleft,hright,if_true]
      rw [Nat.cast_choose ℂ (show j≤p by omega),Nat.cast_choose ℂ (show j+1≤p by omega),
        show p-j=k+1 by omega,show p-(j+1)=k by omega]
      simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_succ,Nat.cast_one]
      have hj : (j+1:ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero j
      have hk : (k+1:ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero k
      field_simp [hj,hk,hfac] <;> ring

/-- Literal paper weight expressed in positive factorial roots. -/
theorem paperPairWeight_factorial_roots (p j k : ℕ) :
    (paperPairWeight p j k : ℂ) = factorialRootNat p /
      ((Real.sqrt (2:ℝ):ℂ)^p * factorialRootNat j * factorialRootNat k) := by
  have hp (n : ℕ) : Real.sqrt ((2:ℝ)^n) = (Real.sqrt (2:ℝ))^n := by
    induction n with
    | zero => norm_num
    | succ n ih => rw [pow_succ,Real.sqrt_mul (by positivity) _,ih,pow_succ]
  unfold paperPairWeight factorialRootNat
  rw [Real.sqrt_div (Nat.cast_nonneg _) _,Real.sqrt_mul (by positivity) _,
    Real.sqrt_mul (by positivity) _,hp]
  push_cast <;> rfl

/-- Exact first-row identity with the original signed unordered pair coefficient. -/
theorem s45_first_relative (p j k : ℕ) (hjk : j+k=p+1) :
    (Real.sqrt (2:ℝ):ℂ) * s45 1 (p+1) j =
      ((j:ℂ)-(k:ℂ)) * (paperPairWeight p j k : ℂ) := by
  let z : Fin (p+1+1) := ⟨1,by omega⟩
  let i : Fin (p+1+1) := ⟨j,by omega⟩
  have he := coefficient45_eq_coeff (p+1) z i
  rw [couplingPolynomial45_eq_paper] at he
  have hroot1 : factorialRootNat 1=1 := by norm_num [factorialRootNat]
  have hk : p+1-j=k := by omega
  simp only [z,i,Nat.add_sub_cancel,hk,hroot1,one_mul,pow_one,smul_pow,
    smul_mul_smul_comm,MvPolynomial.coeff_smul,smul_eq_mul,
    difference_sum_power_coeff p j k hjk] at he
  rw [← s45_in_range] at he
  change s45 1 (p+1) j = _ at he
  rw [he,paperPairWeight_factorial_roots]
  have hs (n : ℕ) : (factorialRootNat n)^2=(n.factorial:ℂ) := by
    unfold factorialRootNat
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg n.factorial)
  rw [← hs p,← hs j,← hs k]
  have hn : (Real.sqrt (2:ℝ):ℂ)≠0 := by norm_num
  simp only [inv_pow]
  field_simp [factorialRootNat_ne_zero,hn] <;> ring

#print axioms difference_sum_power_coeff
#print axioms paperPairWeight_factorial_roots
#print axioms s45_first_relative
end TorusLean.Shared.FermionLocalJet.FourCoupling
