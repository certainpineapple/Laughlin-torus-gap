import torus.shared.BosonFiniteCertificateNatCOMTail

/-! Genuine unbounded-label lowering and the COM oscillator algebra. The
commutator is first proved on the entire polynomial core as the particle
Euler derivation, then specialized to every bihomogeneous particle/orbital
degree-(3,d) polynomial. No orbital cutoff occurs in these definitions or iterates. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation

def canonicalCOMLowerNat : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  (MvPolynomial.mkDerivation ℂ (fun j : ℕ =>
    (Real.sqrt (j : ℝ) : ℂ) • (MvPolynomial.X (j-1) : Core ℕ ℂ))).toLinearMap

def particleEulerNat : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  (MvPolynomial.mkDerivation ℂ (fun j : ℕ => (MvPolynomial.X j : Core ℕ ℂ))).toLinearMap

theorem canonicalCOMLowerNat_X (j : ℕ) :
    canonicalCOMLowerNat (MvPolynomial.X j) =
      (Real.sqrt (j : ℝ) : ℂ) • MvPolynomial.X (j-1) :=
  MvPolynomial.mkDerivation_X ℂ _ j

theorem canonicalCOMLowerNat_C (c : ℂ) : canonicalCOMLowerNat (MvPolynomial.C c) = 0 :=
  MvPolynomial.derivation_C _ c

theorem canonicalCOMLowerNat_mul (p q : Core ℕ ℂ) :
    canonicalCOMLowerNat (p*q) = canonicalCOMLowerNat p*q+p*canonicalCOMLowerNat q := by
  simpa only [canonicalCOMLowerNat,Derivation.coeFn_coe,smul_eq_mul,mul_comm,add_comm] using
    (MvPolynomial.mkDerivation ℂ (fun j : ℕ =>
      (Real.sqrt (j : ℝ) : ℂ) • (MvPolynomial.X (j-1) : Core ℕ ℂ))).leibniz p q

theorem particleEulerNat_X (j : ℕ) : particleEulerNat (MvPolynomial.X j) = MvPolynomial.X j :=
  MvPolynomial.mkDerivation_X ℂ _ j

theorem particleEulerNat_C (c : ℂ) : particleEulerNat (MvPolynomial.C c) = 0 :=
  MvPolynomial.derivation_C _ c

theorem particleEulerNat_mul (p q : Core ℕ ℂ) :
    particleEulerNat (p*q) = particleEulerNat p*q+p*particleEulerNat q := by
  simpa only [particleEulerNat,Derivation.coeFn_coe,smul_eq_mul,mul_comm,add_comm] using
    (MvPolynomial.mkDerivation ℂ (fun j : ℕ => (MvPolynomial.X j : Core ℕ ℂ))).leibniz p q

private theorem natCOM_root_square (j : ℕ) :
    (Real.sqrt (j : ℝ) : ℂ) * (Real.sqrt (j : ℝ) : ℂ) = (j : ℂ) := by
  exact_mod_cast Real.mul_self_sqrt (show (0:ℝ) ≤ j by positivity)

theorem canonicalCOMNat_commutator_X (j : ℕ) :
    canonicalCOMLowerNat (canonicalCOMRaiseNat (MvPolynomial.X j)) -
      canonicalCOMRaiseNat (canonicalCOMLowerNat (MvPolynomial.X j)) = MvPolynomial.X j := by
  cases j with
  | zero =>
    simp [canonicalCOMRaiseNat_X,canonicalCOMLowerNat_X,map_smul]
  | succ j =>
    simp only [canonicalCOMRaiseNat_X,canonicalCOMLowerNat_X,map_smul,
      Nat.add_sub_cancel,Nat.succ_sub_one,smul_smul]
    have hcast (n : ℕ) : (Real.sqrt (n+1 : ℝ) : ℂ) = (Real.sqrt ((n+1 : ℕ) : ℝ) : ℂ) := by
      norm_cast
    simp only [hcast,natCOM_root_square]
    norm_cast
    module

theorem canonicalCOMNat_commutator_mul (p q : Core ℕ ℂ) :
    canonicalCOMLowerNat (canonicalCOMRaiseNat (p*q)) -
      canonicalCOMRaiseNat (canonicalCOMLowerNat (p*q)) =
      (canonicalCOMLowerNat (canonicalCOMRaiseNat p)-canonicalCOMRaiseNat (canonicalCOMLowerNat p))*q +
      p*(canonicalCOMLowerNat (canonicalCOMRaiseNat q)-canonicalCOMRaiseNat (canonicalCOMLowerNat q)) := by
  simp only [canonicalCOMRaiseNat_mul,canonicalCOMLowerNat_mul,map_add]
  ring

/-- Actual commutator on all polynomials, with no particle-number premise. -/
theorem canonicalCOMNat_commutator (p : Core ℕ ℂ) :
    canonicalCOMLowerNat (canonicalCOMRaiseNat p) -
      canonicalCOMRaiseNat (canonicalCOMLowerNat p) = particleEulerNat p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp only [canonicalCOMRaiseNat_C,canonicalCOMLowerNat_C,particleEulerNat_C,map_zero,sub_zero]
  | add p q hp hq =>
    simp only [map_add]
    rw [add_sub_add_comm,hp,hq]
  | mul_X p j hp =>
    rw [canonicalCOMNat_commutator_mul,hp,canonicalCOMNat_commutator_X,
      particleEulerNat_mul,particleEulerNat_X]

theorem particleEulerNat_word (s : List ℕ) :
    particleEulerNat (wordPolynomial s) = (s.length : ℂ) • wordPolynomial s := by
  induction s with
  | nil => simpa only [wordPolynomial_nil,List.length_nil,Nat.cast_zero,zero_smul,map_one] using particleEulerNat_C 1
  | cons j s ih =>
    rw [wordPolynomial_cons,particleEulerNat_mul,particleEulerNat_X,ih]
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one,mul_smul_comm]
    module

theorem particleEulerNat_three_span (d : ℕ) (f : Core ℕ ℂ)
    (hf : f ∈ threeWordDegreeSpanNat d) : particleEulerNat f = (3:ℂ) • f := by
  have hs : threeWordDegreeSpanNat d ≤ LinearMap.ker
      (particleEulerNat - (3:ℂ) • LinearMap.id) := by
    apply Submodule.span_le.mpr
    rintro g ⟨s,hlen,hsum,rfl⟩
    change particleEulerNat (scaledWord factorialRootNat s) - (3:ℂ) • scaledWord factorialRootNat s = 0
    rw [scaledWord,map_smul,particleEulerNat_word,hlen]
    simp only [Nat.cast_ofNat,scaledWord,smul_smul,mul_comm,sub_self]
  have hz := hs hf
  simpa only [LinearMap.mem_ker,LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply,sub_eq_zero] using hz

theorem canonicalCOMNat_ccr_three (d : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d) :
    canonicalCOMLowerNat (canonicalCOMRaiseNat f) =
      canonicalCOMRaiseNat (canonicalCOMLowerNat f) + (3:ℂ) • f := by
  have h := canonicalCOMNat_commutator f
  rw [particleEulerNat_three_span d f (homogeneous_mem_threeWordDegreeSpanNat d f hN hd)] at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

/-- All genuine COM descendants of a true relative vacuum satisfy the
unnormalized oscillator lowering coefficient 3(k+1). -/
theorem canonicalCOMNat_lower_iterate (d k : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d)
    (hL : canonicalCOMLowerNat f = 0) :
    canonicalCOMLowerNat ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k+1] f) =
      (3*((k:ℂ)+1)) • ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k] f) := by
  induction k with
  | zero =>
    simpa only [Function.iterate_one,Function.iterate_zero,Function.id_def,Nat.cast_zero,
      zero_add,mul_one,hL,map_zero,zero_add] using canonicalCOMNat_ccr_three d f hN hd
  | succ k ih =>
    have hh := canonicalCOMRaiseNat_iterate_bihomogeneous d (k+1) f hN hd
    rw [Function.iterate_succ_apply',canonicalCOMNat_ccr_three (d+(k+1)) _ hh.1 hh.2,ih,map_smul]
    rw [show canonicalCOMRaiseNat ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k] f) =
      (canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[k+1] f from
        (Function.iterate_succ_apply' _ _ _).symm]
    simp only [Nat.cast_add,Nat.cast_one]
    module

#print axioms canonicalCOMNat_commutator
#print axioms canonicalCOMNat_ccr_three
#print axioms canonicalCOMNat_lower_iterate
end TorusLean.BosonFiniteCertificate
