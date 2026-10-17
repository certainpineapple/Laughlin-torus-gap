import torus.shared.FermionLocalJetFourCouplingWedge
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Data.Nat.Choose.Cast

/-! Exact original target-copy coefficients. The highest relative row is the
original normalized binomial C_d coefficient, with its (d-p) sign unchanged.
These are identities of the already independently defined s45 polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.RelativeJetMap TorusLean.Shared.ChargeTwoScaling
open scoped BigOperators ComplexConjugate

/-- Coefficient of the literal two-variable linear form, in the full degree sector. -/
theorem linearForm_power_coeff (a b : ℂ) (j k : ℕ) :
    (((a • MvPolynomial.X 0+b • MvPolynomial.X 1 : Core (Fin 2) ℂ)^(j+k)).coeff
      (twoExponent j k)) = ((j+k).choose j : ℂ) * a^j * b^k := by
  classical
  have ht : (twoExponent j k).sum (fun _ m => m)=j+k := by
    rw [Finsupp.sum_fintype _ _ (by simp)]
    simp [twoExponent,Fin.sum_univ_two]
  have hm : (twoExponent j k).multinomial=(j+k).choose j := by
    rw [Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _),
      Finset.univ_fin2,Nat.binomial_eq_choose Fin.zero_ne_one]
    simp [twoExponent]
  have h := MvPolynomial.coeff_linearCombination_X_pow_of_fintype
    ![a,b] (twoExponent j k) (j+k)
  rw [ht,if_pos rfl,hm,Finsupp.prod_fintype _ _ (by simp)] at h
  simpa [Fin.sum_univ_two,Fin.prod_univ_two,twoExponent,mul_assoc] using h

/-- Exact positive factorial normalization of a binomial coefficient. -/
theorem choose_factorialRoot_ratio (n p : ℕ) (hp : p≤n) :
    factorialRootNat p * factorialRootNat (n-p) / factorialRootNat n * (n.choose p : ℂ) =
      (Real.sqrt (n.choose p : ℝ) : ℂ) := by
  calc
    _ = (n.choose p : ℂ) * factorialRootNat p * factorialRootNat (n-p) / factorialRootNat n := by ring
    _ = _ := sqrt_choose_factorial n p hp

/-- The exact original signed normalized binomial, for every natural degree. -/
theorem s45_highest_relative (d p : ℕ) (hp : p≤d) :
    s45 d d p = relativeBinomialCoeff d p := by
  let z : Fin (d+1) := ⟨d,by omega⟩
  let i : Fin (d+1) := ⟨p,by omega⟩
  have he := coefficient45_eq_coeff d z i
  rw [couplingPolynomial45_eq_paper] at he
  have hroot0 : factorialRootNat 0=1 := by norm_num [factorialRootNat]
  have hc : (((MvPolynomial.X 0-MvPolynomial.X 1 : Core (Fin 2) ℂ)^d).coeff
      (twoExponent p (d-p))) = (d.choose p : ℂ) * (-1:ℂ)^(d-p) := by
    have h := linearForm_power_coeff 1 (-1) p (d-p)
    simpa only [one_smul,neg_one_smul,← sub_eq_add_neg,Nat.add_sub_of_le hp,one_pow,mul_one] using h
  simp only [z,i,Nat.sub_self,hroot0,mul_one,pow_zero,smul_pow,
    MvPolynomial.coeff_smul,smul_eq_mul,hc] at he
  have hi : (Real.sqrt (2:ℝ):ℂ)⁻¹ = (scale:ℂ)/2 := by
    simpa only [scale] using scale_div_two_eq_inv.symm
  have hn := choose_factorialRoot_ratio d p hp
  rw [← s45_in_range] at he
  change s45 d d p = _ at he
  rw [he,relativeBinomialCoeff,hi]
  calc
    _ = (-1:ℂ)^(d-p) *
        (factorialRootNat p * factorialRootNat (d-p) / factorialRootNat d * (d.choose p:ℂ)) *
          ((scale:ℂ)/2)^d := by ring
    _ = _ := by rw [hn]

#print axioms linearForm_power_coeff
#print axioms choose_factorialRoot_ratio
#print axioms s45_highest_relative
end TorusLean.Shared.FermionLocalJet.FourCoupling
