import torus.shared.BosonFiniteCertificateNatPairNormalizedRank
import torus.shared.BosonFiniteCertificateNatCOMOccupationAdjoint
import torus.shared.ThermalCoherentJacobiAlgebra

/-! All-degree relative resolution of the actual Nat pair Hamiltonian.
The marked insertion vectors are the original symmetric polynomial images.
Their vacuum pairings follow from the proved occupation adjoint of the genuine
Nat raising and lowering derivations. No isometry of the marked insertion,
compressed Hamiltonian, or invariant-relative-space premise is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open scoped BigOperators

theorem markedBasisInsertion_vacuum_step (p j : ℕ) (f : Core ℕ ℂ)
    (hL : canonicalCOMLowerNat f=0) :
    natOccupationInner (markedBasisInsertion (p+1) j) f =
      -natOccupationInner (markedBasisInsertion p (j+1)) f := by
  have h := canonicalCOMRaiseNat_adjoint (markedBasisInsertion p j) f
  rw [markedBasisInsertion_raise,natOccupationInner_add_left,hL,natOccupationInner_zero_right] at h
  exact eq_neg_of_add_eq_zero_left h

theorem markedBasisInsertion_vacuum_pairing (p j : ℕ) (f : Core ℕ ℂ)
    (hL : canonicalCOMLowerNat f=0) :
    natOccupationInner (markedBasisInsertion p j) f =
      (-1:ℂ)^p * natOccupationInner (markedBasisInsertion 0 (p+j)) f := by
  induction p generalizing j with
  | zero => simp
  | succ p ih =>
    rw [markedBasisInsertion_vacuum_step p j f hL,ih (j+1),pow_succ]
    have he : p+(j+1)=p+1+j := by omega
    rw [he]
    ring

theorem markedRelative_power_binomial (d : ℕ) :
    markedRelative^d = ∑ p ∈ Finset.range (d+1),
      ((d.choose p:ℂ)*(-1:ℂ)^p*(2:ℂ)^(d-p)) •
        ((MvPolynomial.X 0)^p*(MvPolynomial.X 1)^(d-p)) := by
  rw [markedRelative,add_pow]
  apply Finset.sum_congr rfl
  intro p hp
  rw [neg_pow,smul_pow]
  simp only [MvPolynomial.smul_eq_C_mul,map_mul,map_pow,map_natCast,map_neg,map_one,map_ofNat]
  ring

theorem w3RelativeSeed_binomial (d : ℕ) :
    w3RelativeSeed d = (Real.sqrt ((6:ℝ)^d*(d.factorial:ℝ)):ℂ)⁻¹ •
      ∑ p ∈ Finset.range (d+1),
        ((d.choose p:ℂ)*(-1:ℂ)^p*(2:ℂ)^(d-p)) • markedBasisInsertion p (d-p) := by
  rw [w3RelativeSeed,markedRelative_power_binomial,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [map_smul,markedW3_Xpow_mul_Xpow]

theorem relative_binomial_sum (d : ℕ) :
    (∑ p ∈ Finset.range (d+1), (d.choose p:ℂ)*(2:ℂ)^(d-p))=(3:ℂ)^d := by
  have h := add_pow (1:ℂ) 2 d
  norm_num only [one_pow,one_mul,show (1:ℂ)+2=3 by norm_num] at h
  simpa only [mul_comm] using h.symm

theorem w3RelativeSeed_vacuum_pairing (d : ℕ) (f : Core ℕ ℂ)
    (hL : canonicalCOMLowerNat f=0) :
    natOccupationInner (w3RelativeSeed d) f =
      (Real.sqrt ((6:ℝ)^d*(d.factorial:ℝ)):ℂ)⁻¹ * (3:ℂ)^d *
        natOccupationInner (markedBasisInsertion 0 d) f := by
  rw [w3RelativeSeed_binomial,natOccupationInner_smul_left,natOccupationInner_sum_left]
  have hr : star ((Real.sqrt ((6:ℝ)^d*(d.factorial:ℝ)):ℂ)⁻¹) =
      (Real.sqrt ((6:ℝ)^d*(d.factorial:ℝ)):ℂ)⁻¹ := by simp
  rw [hr]
  have he : (∑ p ∈ Finset.range (d+1),
      natOccupationInner (((d.choose p:ℂ)*(-1:ℂ)^p*(2:ℂ)^(d-p)) •
        markedBasisInsertion p (d-p)) f) =
      (3:ℂ)^d * natOccupationInner (markedBasisInsertion 0 d) f := by
    rw [←relative_binomial_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    have hp' : p≤d := Nat.le_of_lt_succ (Finset.mem_range.mp hp)
    rw [natOccupationInner_smul_left,markedBasisInsertion_vacuum_pairing p (d-p) f hL,
      Nat.add_sub_of_le hp']
    simp only [star_mul,star_pow,star_natCast,star_neg,star_one,star_ofNat]
    have hs : (-1:ℂ)^p*(-1:ℂ)^p=1 := by rw [←mul_pow]; norm_num
    calc
      _ = (d.choose p:ℂ)*(2:ℂ)^(d-p)*
          ((-1:ℂ)^p*(-1:ℂ)^p)*natOccupationInner (markedBasisInsertion 0 d) f := by ring
      _ = _ := by rw [hs]; ring
  rw [he,mul_assoc]

/-- The actual normalized pair/spectator vector is a real scalar multiple of
its marked unnormalized source. -/
def natMarkedNormalization (p j : ℕ) : ℂ :=
  (Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ)):ℂ)⁻¹*(factorialRootNat j)⁻¹

theorem pairCOMSeed_spectator_eq_marked (p j : ℕ) :
    pairCOMSeed p*MvPolynomial.X j=natMarkedNormalization p j • markedBasisInsertion p j := by
  exact (markedW3_normalized_pair_spectator p j).symm.trans (by
    rw [map_smul,markedW3_Xpow_mul_Xpow]; rfl)

theorem natMarkedNormalization_real (p j : ℕ) :
    star (natMarkedNormalization p j)=natMarkedNormalization p j := by
  simp [natMarkedNormalization,factorialRootNat]

theorem natMarkedNormalization_sq (p j : ℕ) :
    (natMarkedNormalization p j)^2=((2:ℂ)^p*(p.factorial:ℂ)*(j.factorial:ℂ))⁻¹ := by
  have hA : (Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ)):ℂ)^2=(2:ℂ)^p*(p.factorial:ℂ) := by
    exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤2^p*(p.factorial:ℝ) by positivity)
  have hB : (factorialRootNat j)^2=(j.factorial:ℂ) := by
    unfold factorialRootNat
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg j.factorial)
  rw [natMarkedNormalization,mul_pow,inv_pow,inv_pow,hA,hB,mul_inv_rev]
  ring

theorem natMarkedNormalization_degree_sq (d p : ℕ) (hp : p≤d) :
    (natMarkedNormalization p (d-p))^2 =
      (d.choose p:ℂ)*(2:ℂ)^(d-p)/((2:ℂ)^d*(d.factorial:ℂ)) := by
  rw [natMarkedNormalization_sq]
  have hc : (d.choose p:ℂ)*(p.factorial:ℂ)*((d-p).factorial:ℂ)=(d.factorial:ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hp
  have he : (2:ℂ)^p*(2:ℂ)^(d-p)=(2:ℂ)^d := by rw [←pow_add,Nat.add_sub_of_le hp]
  have hf (n : ℕ) : (n.factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  apply (eq_div_iff (mul_ne_zero (pow_ne_zero _ (by norm_num)) (hf d))).mpr
  rw [←hc,←he]
  field_simp [hf]
  <;> ring

/-- Full actual Hamiltonian action on every relative polynomial in every
three-particle homogeneous orbital degree. This is an identity in the entire
Nat polynomial core, and not just equality of compressed quadratic forms. -/
theorem canonicalPairHamiltonianNat_relative_rank_action (d : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d)
    (hL : canonicalCOMLowerNat f=0) :
    canonicalPairHamiltonianNat f = natOccupationInner (w3RelativeSeed d) f • w3RelativeSeed d := by
  rw [canonicalPairHamiltonianNat_normalized_rank_action d f hN hd,nat_pair_list_range_sum,
    w3RelativeSeed_vacuum_pairing d f hL,w3RelativeSeed_binomial,smul_smul,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p≤d := Nat.le_of_lt_succ (Finset.mem_range.mp hp)
  rw [pairCOMSeed_spectator_eq_marked,natOccupationInner_smul_left,
    natMarkedNormalization_real,markedBasisInsertion_vacuum_pairing p (d-p) f hL,
    Nat.add_sub_of_le hp',smul_smul,smul_smul]
  congr 1
  have hs : (Real.sqrt ((6:ℝ)^d*(d.factorial:ℝ)):ℂ)^2=(6:ℂ)^d*(d.factorial:ℂ) := by
    exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤6^d*(d.factorial:ℝ) by positivity)
  have hf : (d.factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  have h6 : (6:ℂ)^d=(2:ℂ)^d*(3:ℂ)^d := by rw [←mul_pow]; norm_num
  calc
    _ = (natMarkedNormalization p (d-p))^2 * (-1:ℂ)^p *
        natOccupationInner (markedBasisInsertion 0 d) f := by ring
    _ = _ := by
      rw [natMarkedNormalization_degree_sq d p hp']
      have hi : (Real.sqrt ((6:ℝ)^d*(d.factorial:ℝ)):ℂ)⁻¹ ^ 2 =
          ((2:ℂ)^d*(3:ℂ)^d*(d.factorial:ℂ))⁻¹ := by rw [inv_pow,hs,h6]
      calc
        _ = ((2:ℂ)^d*(3:ℂ)^d*(d.factorial:ℂ))⁻¹ * (3:ℂ)^d *
            (d.choose p:ℂ)*(-1:ℂ)^p*(2:ℂ)^(d-p)*
            natOccupationInner (markedBasisInsertion 0 d) f := by
          field_simp [hf] <;> ring
        _ = _ := by rw [←hi]; ring

#print axioms markedBasisInsertion_vacuum_pairing
#print axioms w3RelativeSeed_vacuum_pairing
#print axioms canonicalPairHamiltonianNat_relative_rank_action
end TorusLean.BosonFiniteCertificate
