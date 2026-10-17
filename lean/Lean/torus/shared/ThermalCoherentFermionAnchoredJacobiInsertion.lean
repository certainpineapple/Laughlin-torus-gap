import torus.shared.ThermalCoherentFermionAnchoredSource
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Module

/-! Finite marked pair/spectator polynomials inserted into the *existing*
Nat exterior algebra. The insertion is linear, not an algebra homomorphism:
its monomial images are the actual v_p wedge e_j. No injectivity, isometry,
relative orthogonality, or new oscillator/exterior model is assumed. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchored
open TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators

abbrev FermionMarkedOscillator := MvPolynomial (Fin 2) ℂ

def markedPair : FermionMarkedOscillator := MvPolynomial.X 0

def markedSpectator : FermionMarkedOscillator := MvPolynomial.X 1

def fermionMarkedCOM : FermionMarkedOscillator := markedPair + markedSpectator

/-- This sign is the original (-1)^(d-p) paper orientation. -/
def fermionMarkedRelative : FermionMarkedOscillator := markedPair - (2:ℂ) • markedSpectator

def fermionMarkedBasisInsertion (p j : ℕ) : FormalExterior :=
  ((Real.sqrt ((2:ℝ)^p * (p.factorial:ℝ)):ℂ) *
    (Real.sqrt (j.factorial:ℝ):ℂ)) • formalThreeSeed p j

def fermionMarkedW3 : FermionMarkedOscillator →ₗ[ℂ] FormalExterior :=
  (Finsupp.linearCombination ℂ (fun n : Fin 2 →₀ ℕ =>
    fermionMarkedBasisInsertion (n 0) (n 1))).comp
      (AddMonoidAlgebra.coeffLinearEquiv ℂ).toLinearMap

theorem fermionMarkedW3_monomial (n : Fin 2 →₀ ℕ) (c : ℂ) :
    fermionMarkedW3 (MvPolynomial.monomial n c) =
      c • fermionMarkedBasisInsertion (n 0) (n 1) := by
  change Finsupp.linearCombination ℂ
    (fun m : Fin 2 →₀ ℕ => fermionMarkedBasisInsertion (m 0) (m 1))
      (Finsupp.single n c) = _
  simp only [Finsupp.linearCombination_single]

theorem fermionMarkedW3_pair_spectator (p j : ℕ) :
    fermionMarkedW3 (markedPair^p * markedSpectator^j) =
      fermionMarkedBasisInsertion p j := by
  simp only [markedPair,markedSpectator,MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul_monomial,mul_one,fermionMarkedW3_monomial,
    Finsupp.add_apply,Finsupp.single_apply]
  norm_num

theorem fermionMarkedW3_normalized_pair_spectator (p j : ℕ) :
    fermionMarkedW3 (((Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ)):ℂ)⁻¹ *
      (Real.sqrt (j.factorial:ℝ):ℂ)⁻¹) • (markedPair^p*markedSpectator^j)) =
        formalThreeSeed p j := by
  have hp : (Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ)):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  have hj : (Real.sqrt (j.factorial:ℝ):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  rw [map_smul,fermionMarkedW3_pair_spectator,fermionMarkedBasisInsertion,smul_smul]
  rw [show ((Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ)):ℂ)⁻¹ *
      (Real.sqrt (j.factorial:ℝ):ℂ)⁻¹) *
      ((Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ)):ℂ) *
      (Real.sqrt (j.factorial:ℝ):ℂ))=1 by field_simp]
  exact one_smul _ _

/-- The true v_0 wedge e_l column, including its negative pair sign. -/
theorem formalAnchoredSeed_eq_marked (l : ℕ) :
    formalAnchoredSeed l = (Real.sqrt (l.factorial:ℝ):ℂ)⁻¹ •
      fermionMarkedW3 (markedSpectator^l) := by
  have h := fermionMarkedW3_normalized_pair_spectator 0 l
  simpa only [formalAnchoredSeed,pow_zero,one_mul,Nat.factorial_zero,
    Nat.cast_one,mul_one,Real.sqrt_one,Complex.ofReal_one,inv_one,
    map_smul] using h.symm

def fermionMarkedDifference : FermionMarkedOscillator →ₗ[ℂ] FermionMarkedOscillator :=
  (MvPolynomial.pderiv 0).toLinearMap - (MvPolynomial.pderiv 1).toLinearMap

/-- The original two-column bra polynomial: T (∂A−∂B)−1. -/
def fermionMarkedEuler (f : FermionMarkedOscillator) : FermionMarkedOscillator :=
  fermionMarkedRelative * fermionMarkedDifference f - f

theorem fermionMarkedDifference_mul (f g : FermionMarkedOscillator) :
    fermionMarkedDifference (f*g) =
      fermionMarkedDifference f*g + f*fermionMarkedDifference g := by
  change MvPolynomial.pderiv 0 (f*g) - MvPolynomial.pderiv 1 (f*g) =
    (MvPolynomial.pderiv 0 f - MvPolynomial.pderiv 1 f)*g +
      f*(MvPolynomial.pderiv 0 g - MvPolynomial.pderiv 1 g)
  rw [MvPolynomial.pderiv_mul,MvPolynomial.pderiv_mul]
  ring

theorem fermionMarkedDifference_COM : fermionMarkedDifference fermionMarkedCOM=0 := by
  simp [fermionMarkedDifference,fermionMarkedCOM,markedPair,markedSpectator]

theorem fermionMarkedDifference_relative :
    fermionMarkedDifference fermionMarkedRelative=(3:FermionMarkedOscillator) := by
  have hc (i : Fin 2) : MvPolynomial.pderiv i (2:FermionMarkedOscillator)=0 := by
    have hC : (MvPolynomial.C (2:ℂ):FermionMarkedOscillator)=2 := by
      simp only [map_ofNat]
    rw [←hC]
    exact MvPolynomial.pderiv_C
  simp [fermionMarkedDifference,fermionMarkedRelative,markedPair,markedSpectator,
    Derivation.map_smul,MvPolynomial.smul_eq_C_mul,map_ofNat,hc]
  norm_num

theorem fermionMarkedDifference_pow (f : FermionMarkedOscillator) (d : ℕ) :
    fermionMarkedDifference (f^d) = (d:ℂ) • (f^(d-1)*fermionMarkedDifference f) := by
  change MvPolynomial.pderiv 0 (f^d) - MvPolynomial.pderiv 1 (f^d) =
    (d:ℂ) • (f^(d-1)*(MvPolynomial.pderiv 0 f - MvPolynomial.pderiv 1 f))
  rw [MvPolynomial.pderiv_pow,MvPolynomial.pderiv_pow]
  simp only [MvPolynomial.smul_eq_C_mul,map_natCast]
  ring

/-- A genuine differential diagonalization on the finite marked source. -/
theorem fermionMarkedEuler_jacobi (n d : ℕ) :
    fermionMarkedEuler (fermionMarkedCOM^n*fermionMarkedRelative^d) =
      (3*(d:ℂ)-1) • (fermionMarkedCOM^n*fermionMarkedRelative^d) := by
  rw [fermionMarkedEuler,fermionMarkedDifference_mul,fermionMarkedDifference_pow,
    fermionMarkedDifference_pow,fermionMarkedDifference_COM,
    fermionMarkedDifference_relative]
  simp only [mul_zero,smul_zero,zero_mul,zero_add]
  cases d with
  | zero => simp
  | succ d =>
    simp only [Nat.succ_eq_add_one,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,
      pow_succ,MvPolynomial.smul_eq_C_mul,map_sub,map_mul,map_ofNat,map_natCast,map_one]
    ring

theorem fermionMarkedEuler_pair_power (l : ℕ) :
    fermionMarkedEuler (markedPair^l) =
      (l:ℂ) • (fermionMarkedRelative*markedPair^(l-1)) - markedPair^l := by
  have hp : fermionMarkedDifference markedPair=1 := by
    simp [fermionMarkedDifference,markedPair]
  rw [fermionMarkedEuler,fermionMarkedDifference_pow,hp,mul_one,mul_smul_comm]

/-- Both actual normalized exterior columns are retained. The l=0,1
vanishing follows from exterior multiplication, not deleted matrix rows. -/
def formalConnectedAnchoredSeed (l : ℕ) : FormalExterior :=
  ((2:ℂ)^l * (Real.sqrt (l.factorial:ℝ):ℂ))⁻¹ •
    fermionMarkedW3 (fermionMarkedEuler (markedPair^l))

theorem formalConnectedAnchoredSeed_zero : formalConnectedAnchoredSeed 0=0 := by
  rw [formalConnectedAnchoredSeed,fermionMarkedEuler_pair_power]
  simp only [pow_zero,Nat.cast_zero,zero_smul,zero_sub,map_neg]
  have h := fermionMarkedW3_pair_spectator 0 0
  simp only [pow_zero,mul_one,fermionMarkedBasisInsertion,Nat.factorial_zero,
    Nat.cast_one,Real.sqrt_one,Complex.ofReal_one,one_smul] at h
  rw [h]
  have hz : formalThreeSeed 0 0=0 := by
    simpa only [formalAnchoredSeed] using formalAnchoredSeed_zero
  rw [hz,neg_zero,smul_zero]


/-- Expanding the differential bra exhibits its two original source monomials. -/
theorem fermionMarkedEuler_pair_succ (p : ℕ) :
    fermionMarkedEuler (markedPair^(p+1)) =
      (p:ℂ) • (markedPair^(p+1)*markedSpectator^0) -
      (2*((p:ℂ)+1)) • (markedPair^p*markedSpectator^1) := by
  rw [fermionMarkedEuler_pair_power]
  simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,fermionMarkedRelative,
    pow_zero,pow_one,mul_one,pow_succ,MvPolynomial.smul_eq_C_mul,
    map_mul,map_natCast,map_add,map_one,map_ofNat]
  ring

/-- Actual exterior two-column source with every factorial normalization
shown explicitly. The columns are v_(l-1) wedge e_1 and v_l wedge e_0. -/
theorem formalConnectedAnchoredSeed_two_columns (p : ℕ) :
    formalConnectedAnchoredSeed (p+1) =
      ((2:ℂ)^(p+1)*(Real.sqrt ((p+1).factorial:ℝ):ℂ))⁻¹ •
        (((p:ℂ)*(Real.sqrt ((2:ℝ)^(p+1)*((p+1).factorial:ℝ)):ℂ)) •
            formalThreeSeed (p+1) 0 -
          ((2*((p:ℂ)+1))*(Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ)):ℂ)) •
            formalThreeSeed p 1) := by
  rw [formalConnectedAnchoredSeed,fermionMarkedEuler_pair_succ,map_sub,map_smul,
    map_smul,fermionMarkedW3_pair_spectator,fermionMarkedW3_pair_spectator]
  simp only [fermionMarkedBasisInsertion,Nat.factorial_zero,Nat.factorial_one,
    Nat.cast_one,Real.sqrt_one,Complex.ofReal_one,mul_one,smul_smul]

/-- The second repeated low-level exterior source is zero as a vector. -/
theorem formalConnectedAnchoredSeed_one : formalConnectedAnchoredSeed 1=0 := by
  have h := formalConnectedAnchoredSeed_two_columns 0
  have hz : formalThreeSeed 0 1=0 := by
    simpa only [formalAnchoredSeed] using formalAnchoredSeed_one
  simpa only [Nat.zero_add,Nat.cast_zero,zero_mul,zero_smul,hz,smul_zero,
    sub_zero] using h


/-- The charge-two/charge-one marked lowering annihilates the original
relative direction. Its transfer to exterior word lowering is separate. -/
theorem fermionMarkedRelative_lower_power (d : ℕ) :
    (2:ℂ) • MvPolynomial.pderiv 0 (fermionMarkedRelative^d) +
      MvPolynomial.pderiv 1 (fermionMarkedRelative^d)=0 := by
  have h0 : MvPolynomial.pderiv 0 fermionMarkedRelative=1 := by
    simp [fermionMarkedRelative,markedPair,markedSpectator,Derivation.map_smul]
  have h1 : MvPolynomial.pderiv 1 fermionMarkedRelative=(-2:FermionMarkedOscillator) := by
    have hc : MvPolynomial.pderiv 1 (2:FermionMarkedOscillator)=0 := by
      have hC : (MvPolynomial.C (2:ℂ):FermionMarkedOscillator)=2 := by
        simp only [map_ofNat]
      rw [←hC]
      exact MvPolynomial.pderiv_C
    simp [fermionMarkedRelative,markedPair,markedSpectator,Derivation.map_smul,
      MvPolynomial.smul_eq_C_mul,map_ofNat,hc]
  rw [MvPolynomial.pderiv_pow,MvPolynomial.pderiv_pow,h0,h1]
  simp only [MvPolynomial.smul_eq_C_mul,map_ofNat]
  ring

end TorusLean.Shared.ThermalCoherentFermionAnchored
