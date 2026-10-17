import torus.shared.BosonFiniteCertificateNatCOMLower

/-! The same actual Nat COM algebra at arbitrary particle number. This file
uses no finite occupation enumeration and no N=4 certificate or positivity
claim. The algebraic Euler eigenspace statement also covers sums of different
orbital weighted degrees at a fixed particle degree. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson

theorem particleEulerNat_X_pow (j n : ℕ) :
    particleEulerNat ((MvPolynomial.X j)^n) = (n:ℂ) • (MvPolynomial.X j)^n := by
  induction n with
  | zero =>
    simpa only [pow_zero,Nat.cast_zero,zero_smul,map_one] using particleEulerNat_C 1
  | succ n ih =>
    rw [pow_succ,particleEulerNat_mul,ih,particleEulerNat_X]
    simp only [Nat.cast_add,Nat.cast_one,smul_mul_assoc]
    module

theorem particleEulerNat_monomial (n : ℕ →₀ ℕ) (c : ℂ) :
    particleEulerNat (MvPolynomial.monomial n c) = (n.degree:ℂ) • MvPolynomial.monomial n c := by
  apply @Finsupp.induction ℕ ℕ _ _ n
  · simpa only [MvPolynomial.monomial_zero',map_zero,Nat.cast_zero,zero_smul] using particleEulerNat_C c
  · intro j e p _ _ ih
    rw [MvPolynomial.monomial_single_add,particleEulerNat_mul,particleEulerNat_X_pow,ih]
    simp only [map_add,Finsupp.degree_single,Nat.cast_add,smul_mul_assoc,mul_smul_comm]
    module

theorem particleEulerNat_homogeneous (k : ℕ) (f : Core ℕ ℂ) (hN : f.IsHomogeneous k) :
    particleEulerNat f = (k:ℂ) • f := by
  rw [← MvPolynomial.support_sum_monomial_coeff f]
  rw [map_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hc := MvPolynomial.mem_support_iff.mp hn
  have he : n.degree=k := by
    by_contra h
    exact hc (hN.coeff_eq_zero h)
  rw [particleEulerNat_monomial,he]

theorem particleEulerNat_raise_commute (f : Core ℕ ℂ) :
    particleEulerNat (canonicalCOMRaiseNat f) = canonicalCOMRaiseNat (particleEulerNat f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp only [canonicalCOMRaiseNat_C,particleEulerNat_C,map_zero]
  | add f g hf hg => simp only [map_add,hf,hg]
  | mul_X f j hf =>
    simp only [canonicalCOMRaiseNat_mul,particleEulerNat_mul,map_add,
      particleEulerNat_X,canonicalCOMRaiseNat_X,map_smul,hf]
    ring

theorem particleEulerNat_iterate_eigen (c : ℂ) (n : ℕ) (f : Core ℕ ℂ)
    (hE : particleEulerNat f=c • f) :
    particleEulerNat ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] f) =
      c • ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] f) := by
  induction n with
  | zero => exact hE
  | succ n ih =>
    rw [Function.iterate_succ_apply',particleEulerNat_raise_commute,ih,map_smul]

theorem canonicalCOMNat_ccr_eigen (c : ℂ) (f : Core ℕ ℂ)
    (hE : particleEulerNat f=c • f) :
    canonicalCOMLowerNat (canonicalCOMRaiseNat f) =
      canonicalCOMRaiseNat (canonicalCOMLowerNat f)+c • f := by
  have h := canonicalCOMNat_commutator f
  rw [hE] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

theorem canonicalCOMNat_lower_iterate_eigen (c : ℂ) (n : ℕ) (f : Core ℕ ℂ)
    (hE : particleEulerNat f=c • f) (hL : canonicalCOMLowerNat f=0) :
    canonicalCOMLowerNat ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n+1] f) =
      (c*((n:ℂ)+1)) • ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] f) := by
  induction n with
  | zero =>
    simpa only [Function.iterate_one,Function.iterate_zero,Function.id_def,Nat.cast_zero,
      zero_add,mul_one,hL,map_zero,zero_add] using canonicalCOMNat_ccr_eigen c f hE
  | succ n ih =>
    have hh := particleEulerNat_iterate_eigen c (n+1) f hE
    rw [Function.iterate_succ_apply',canonicalCOMNat_ccr_eigen c _ hh,ih,map_smul]
    rw [show canonicalCOMRaiseNat ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] f) =
      (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n+1] f from
        (Function.iterate_succ_apply' _ _ _).symm]
    simp only [Nat.cast_add,Nat.cast_one]
    module

/-- Fixed particle degree alone suffices; there is no orbital-degree premise. -/
theorem canonicalCOMNat_ccr_particle (k : ℕ) (f : Core ℕ ℂ) (hN : f.IsHomogeneous k) :
    canonicalCOMLowerNat (canonicalCOMRaiseNat f) =
      canonicalCOMRaiseNat (canonicalCOMLowerNat f)+(k:ℂ) • f :=
  canonicalCOMNat_ccr_eigen k f (particleEulerNat_homogeneous k f hN)

theorem canonicalCOMNat_lower_iterate_particle (k n : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous k) (hL : canonicalCOMLowerNat f=0) :
    canonicalCOMLowerNat ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n+1] f) =
      ((k:ℂ)*((n:ℂ)+1)) • ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[n] f) :=
  canonicalCOMNat_lower_iterate_eigen k n f (particleEulerNat_homogeneous k f hN) hL

#print axioms particleEulerNat_monomial
#print axioms particleEulerNat_homogeneous
#print axioms canonicalCOMNat_ccr_particle
#print axioms canonicalCOMNat_lower_iterate_particle
end TorusLean.BosonFiniteCertificate
