import torus.shared.FermionCertificateThreePolynomial

/-! Exact equality between the full genuine normalized rotation and the
appendix integer U formula. Positive roots are reconciled by their actual
squares; signs remain entirely in the integer polynomial coefficient. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.ThreeCoupling
open TorusLean.BosonFiniteCertificate
open TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators

private theorem coupling_power_factor (z n p h : ℕ)
    (hhz : h≤z) (hhp : h≤p) (hpn : p-h≤n) :
    couplingU^h*(-couplingV)^(z-h)*couplingV^(p-h)*couplingU^(n-(p-h))=
      (-1:ℂ)^(z-h)*(2:ℂ)^(p-h)*
        ((Real.sqrt (2:ℝ):ℂ)^z/
          ((Real.sqrt (2:ℝ):ℂ)^p*(Real.sqrt (3:ℝ):ℂ)^(z+n))) := by
  have hr : (Real.sqrt (2:ℝ):ℂ)≠0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)))
  have hs : (Real.sqrt (3:ℝ):ℂ)≠0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<3)))
  have hr2 : (Real.sqrt (2:ℝ):ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hrz : (Real.sqrt (2:ℝ):ℂ)^z=
      (Real.sqrt (2:ℝ):ℂ)^h*(Real.sqrt (2:ℝ):ℂ)^(z-h) := by
    rw [← pow_add,Nat.add_sub_of_le hhz]
  have hrp : (Real.sqrt (2:ℝ):ℂ)^p=
      (Real.sqrt (2:ℝ):ℂ)^h*(Real.sqrt (2:ℝ):ℂ)^(p-h) := by
    rw [← pow_add,Nat.add_sub_of_le hhp]
  have hst : (Real.sqrt (3:ℝ):ℂ)^(z+n)=
      (Real.sqrt (3:ℝ):ℂ)^h*(Real.sqrt (3:ℝ):ℂ)^(z-h)*
        (Real.sqrt (3:ℝ):ℂ)^(p-h)*(Real.sqrt (3:ℝ):ℂ)^(n-(p-h)) := by
    rw [← pow_add,← pow_add,← pow_add]
    congr 1
    omega
  have ht : (2:ℂ)^(p-h)=((Real.sqrt (2:ℝ):ℂ)^(p-h))^2 := by
    rw [← hr2,← pow_mul,← pow_mul,Nat.mul_comm]
  rw [neg_pow couplingV (z-h)]
  simp only [couplingU,couplingV,mul_pow,inv_pow]
  rw [hrz,hrp,hst,ht]
  field_simp [hr,hs]
  <;> ring

def positiveCouplingFactor (z T p : ℕ) : ℝ :=
  Real.sqrt (p.factorial:ℝ)*Real.sqrt ((T-p).factorial:ℝ) /
    (Real.sqrt (z.factorial:ℝ)*Real.sqrt ((T-z).factorial:ℝ)) *
      (Real.sqrt (2:ℝ))^z/((Real.sqrt (2:ℝ))^p*(Real.sqrt (3:ℝ))^T)

theorem positiveCouplingFactor_nonneg (z T p : ℕ) : 0≤positiveCouplingFactor z T p := by
  unfold positiveCouplingFactor
  positivity

private theorem square_power (a : ℝ) (n : ℕ) : (a^n)^2=(a^2)^n := by
  rw [← pow_mul,← pow_mul,Nat.mul_comm]

theorem positiveCouplingFactor_sq (z T p : ℕ) :
    (positiveCouplingFactor z T p)^2=(couplingScaleQ z T p:ℝ) := by
  have hf (n : ℕ) : (Real.sqrt (n.factorial:ℝ))^2=(n.factorial:ℝ) :=
    Real.sq_sqrt (by positivity)
  have h2 : (Real.sqrt (2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have h3 : (Real.sqrt (3:ℝ))^2=3 := Real.sq_sqrt (by norm_num)
  unfold positiveCouplingFactor couplingScaleQ
  push_cast
  simp only [div_pow,mul_pow,square_power,hf,h2,h3]
  ring

theorem positiveCouplingFactor_eq_sqrt (z T p : ℕ) :
    positiveCouplingFactor z T p=Real.sqrt (couplingScaleQ z T p:ℝ) := by
  rw [← positiveCouplingFactor_sq,Real.sqrt_sq_eq_abs,
    abs_of_nonneg (positiveCouplingFactor_nonneg z T p)]

/-- Full coefficient formula, not restricted to either original anchor column. -/
theorem coefficientThree_integer_factor (T : ℕ) (z p : Fin (T+1)) :
    coefficientThree T z p=(integerCoupling 2 z.val T p.val:ℂ)*
      (positiveCouplingFactor z.val T p.val:ℂ) := by
  have hz : z.val≤T := Nat.le_of_lt_succ z.isLt
  have hp : p.val≤T := Nat.le_of_lt_succ p.isLt
  rw [coefficientThree_full_sum,integerCoupling,if_pos ⟨hz,hp⟩]
  unfold positiveCouplingFactor
  push_cast
  rw [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have hhz : h≤z.val := Nat.le_of_lt_succ (Finset.mem_range.mp hh)
  split_ifs with hv
  · calc
      _ = (factorialRootNat p.val*factorialRootNat (T-p.val) /
          (factorialRootNat z.val*factorialRootNat (T-z.val))) *
          ((z.val.choose h:ℂ)*((T-z.val).choose (p.val-h):ℂ)) *
          (couplingU^h*(-couplingV)^(z.val-h)*couplingV^(p.val-h)*
            couplingU^(T-z.val-(p.val-h))) := by ring
      _ = _ := by
        rw [coupling_power_factor z.val (T-z.val) p.val h hhz hv.1 hv.2,
          Nat.add_sub_of_le hz]
        simp only [factorialRootNat]
        ring
  · ring

/-- Exact binding of the numerical certificate's sThree to the actual
unitary normalized-monomial coefficient. No table equality is assumed. -/
theorem coefficientThree_eq_sThree (T : ℕ) (z p : Fin (T+1)) :
    coefficientThree T z p=(sThree z.val T p.val:ℂ) := by
  rw [coefficientThree_integer_factor,positiveCouplingFactor_eq_sqrt,sThree]
  push_cast
  rfl

end TorusLean.Shared.FermionLocalJet.ThreeCoupling
