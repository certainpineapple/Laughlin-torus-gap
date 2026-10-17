import torus.shared.FermionCertificateThreeRotation
import torus.shared.FermionLocalJetFourCouplingTargetCoefficients
import Mathlib.Tactic.Module

/-! Direct coefficient expansion of the original two-mode polynomial.
This retains every input p; it is not an anchor-column reconstruction. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators

private theorem twoExponent_le (a b p q : ℕ) :
    twoExponent a b ≤ twoExponent p q ↔ a≤p ∧ b≤q := by
  constructor
  · intro h
    exact ⟨by simpa [twoExponent] using h 0,by simpa [twoExponent] using h 1⟩
  · rintro ⟨ha,hb⟩ i
    fin_cases i
    · simpa [twoExponent] using ha
    · simpa [twoExponent] using hb

private theorem twoExponent_sub (a b p q : ℕ) :
    twoExponent p q-twoExponent a b=twoExponent (p-a) (q-b) := by
  ext i
  fin_cases i <;> simp [twoExponent]

/-- Coefficient convolution, proved before substituting any square root. -/
theorem twoLinearPowers_coeff (a b c d : ℂ) (z n p q : ℕ) (ht : p+q=z+n) :
    (((a • MvPolynomial.X 0+b • MvPolynomial.X 1)^z *
      (c • MvPolynomial.X 0+d • MvPolynomial.X 1)^n : Core (Fin 2) ℂ).coeff
        (twoExponent p q)) =
      ∑ h ∈ Finset.range (z+1), if h≤p ∧ p-h≤n then
        (z.choose h:ℂ)*(n.choose (p-h):ℂ)*a^h*b^(z-h)*c^(p-h)*d^(n-(p-h))
      else 0 := by
  classical
  have he : (a • MvPolynomial.X 0+b • MvPolynomial.X 1 : Core (Fin 2) ℂ)^z =
      ∑ h ∈ Finset.range (z+1), MvPolynomial.monomial (twoExponent h (z-h))
        ((z.choose h:ℂ)*a^h*b^(z-h)) := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro h hh
    simp only [smul_pow,MvPolynomial.X_pow_eq_monomial,smul_mul_smul_comm,
      MvPolynomial.monomial_mul_monomial,mul_one,MvPolynomial.smul_monomial,twoExponent]
    rw [show (Nat.cast (z.choose h) : Core (Fin 2) ℂ) =
      MvPolynomial.C (z.choose h : ℂ) by simp, mul_comm, MvPolynomial.C_mul_monomial]
    congr 1
    ring
  rw [he,Finset.sum_mul,MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have hh' : h≤z := Nat.le_of_lt_succ (Finset.mem_range.mp hh)
  simp only [MvPolynomial.coeff_monomial_mul',twoExponent_le,twoExponent_sub]
  have hc : (h≤p ∧ z-h≤q) ↔ (h≤p ∧ p-h≤n) := by omega
  simp only [hc]
  split_ifs with hvalid
  · have hn : (p-h)+(q-(z-h))=n := by omega
    have hq : q-(z-h)=n-(p-h) := by omega
    have hv := linearForm_power_coeff c d (p-h) (q-(z-h))
    rw [hn] at hv
    rw [hv,hq]
    ring
  · rfl

/-- A total-degree preserving coefficient formula for every original
normalized row, before rational square-root cancellation. -/
theorem coefficientThree_full_sum (T : ℕ) (z p : Fin (T+1)) :
    coefficientThree T z p=
      (factorialRootNat p.val*factorialRootNat (T-p.val) /
        (factorialRootNat z.val*factorialRootNat (T-z.val))) *
      ∑ h ∈ Finset.range (z.val+1), if h≤p.val ∧ p.val-h≤T-z.val then
        (z.val.choose h:ℂ)*((T-z.val).choose (p.val-h):ℂ)*
          couplingU^h*(-couplingV)^(z.val-h)*couplingV^(p.val-h)*
            couplingU^(T-z.val-(p.val-h)) else 0 := by
  have hz : z.val≤T := Nat.le_of_lt_succ z.isLt
  have hp : p.val≤T := Nat.le_of_lt_succ p.isLt
  rw [coefficientThree_eq_coeff,couplingPolynomialThree_eq_paper,MvPolynomial.coeff_smul]
  have hs : (couplingU • MvPolynomial.X 0-couplingV • MvPolynomial.X 1 : Core (Fin 2) ℂ)=
      couplingU • MvPolynomial.X 0+(-couplingV) • MvPolynomial.X 1 := by module
  rw [hs,twoLinearPowers_coeff couplingU (-couplingV) couplingV couplingU
    z.val (T-z.val) p.val (T-p.val) (by omega)]
  simp only [smul_eq_mul,div_eq_mul_inv,mul_assoc]

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
