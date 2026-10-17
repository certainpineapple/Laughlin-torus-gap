import torus.shared.BosonFiniteCertificateNatFourS4Relative
import torus.shared.RelativeJetMapLeibniz

/-! The S4 relative rank vector is the original signed C_d combination of
normalized pair-COM products. This identifies its genuine planar source
with the coefficient pattern of the already independently defined physical
fourBodyJet; no periodization norm or isometry is asserted. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Shared.ThermalCoherentJacobiFourInsertion
open TorusLean.Shared.ThermalCoherentJacobiFourRotation
open TorusLean.Shared.ThermalCoherentJacobiFourParseval
open TorusLean.Shared.ThermalCoherentNatFourHamiltonian
open TorusLean.Shared.RelativeJetMap TorusLean.Shared.ChargeTwoScaling
open scoped BigOperators

def natFourPairRelativeSeed (d : ℕ) : Core ℕ ℂ :=
  ∑ p ∈ Finset.range (d+1), relativeBinomialCoeff d p •
    (pairCOMSeed p*pairCOMSeed (d-p))

private theorem natFour_s4_binomial_scalar (d p : ℕ) (hp : p≤d) :
    (factorialRootNat d)⁻¹*(Real.sqrt (2:ℝ):ℂ)⁻¹^d*(d.choose p:ℂ)*(-1:ℂ)^(d-p)=
      relativeBinomialCoeff d p*(factorialRootNat p*factorialRootNat (d-p))⁻¹ := by
  rw [relativeBinomialCoeff,scale_div_two_eq_inv]
  change _ = (-1:ℂ)^(d-p)*(Real.sqrt (d.choose p:ℝ):ℂ)*
    (Real.sqrt (2:ℝ):ℂ)⁻¹^d*(factorialRootNat p*factorialRootNat (d-p))⁻¹
  rw [←sqrt_choose_factorial d p hp]
  change _ = (-1:ℂ)^(d-p)*((d.choose p:ℂ)*factorialRootNat p*
    factorialRootNat (d-p)/factorialRootNat d)*(Real.sqrt (2:ℝ):ℂ)⁻¹^d*
      (factorialRootNat p*factorialRootNat (d-p))⁻¹
  field_simp [factorialRootNat_ne_zero]
  <;> ring

/-- The highest relative oscillator column is the literal original signed
normalized binomial combination, on the complete two-mode source. -/
theorem natFour_s4_rotated_relative_word (d : ℕ) :
    rotateSpectatorPolynomial (normalizedSpectatorWord 0 d)=
      ∑ p ∈ Finset.range (d+1), relativeBinomialCoeff d p • normalizedSpectatorWord p (d-p) := by
  have he : rotateSpectatorPolynomial (normalizedSpectatorWord 0 d)=
      ((factorialRootNat d)⁻¹*(Real.sqrt (2:ℝ):ℂ)⁻¹^d) •
        ((MvPolynomial.X 0 : Core (Fin 2) ℂ)-MvPolynomial.X 1)^d := by
    simp only [normalizedSpectatorWord,map_smul,map_mul,map_pow,pow_zero,one_mul,
      rotateSpectatorPolynomial_X_one,smul_pow,smul_smul]
    norm_num [factorialRootNat]
  rw [he,sub_eq_add_neg,add_pow,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have ht : ((MvPolynomial.X 0 : Core (Fin 2) ℂ)^p*(-MvPolynomial.X 1)^(d-p)*(d.choose p : Core (Fin 2) ℂ))=
      ((d.choose p:ℂ)*(-1:ℂ)^(d-p)) •
        ((MvPolynomial.X 0)^p*(MvPolynomial.X 1)^(d-p)) := by
    rw [neg_pow]
    simp only [MvPolynomial.smul_eq_C_mul,map_mul,map_pow,map_neg,map_one,map_natCast]
    ring
  rw [ht,normalizedSpectatorWord,smul_smul,smul_smul]
  congr 1
  calc
    _ = (factorialRootNat d)⁻¹*(Real.sqrt (2:ℝ):ℂ)⁻¹^d*(d.choose p:ℂ)*(-1:ℂ)^(d-p) := by ring
    _ = _ := natFour_s4_binomial_scalar d p (Nat.le_of_lt_succ (Finset.mem_range.mp hp))

theorem natFourPairRelativeSeed_eq_marked (d : ℕ) :
    natFourPairRelativeSeed d=w4RelativeSeed 0 d := by
  have h := congrArg (pairSpectatorW4 0) (natFour_s4_rotated_relative_word d)
  rw [pairSpectatorW4_rotatedWord] at h
  simp only [map_sum,map_smul,pairSpectatorW4_normalizedWord,
    ←natFour_pair_product_eq_marked_level] at h
  simpa [natFourPairRelativeSeed,normalizedFourCOMDescendant] using h.symm

/-- Exact independent relative-binomial source form for the actual S4. -/
theorem canonicalNatFourS4_pair_relative_rank_form (d : ℕ) (f g : Core ℕ ℂ)
    (hN : g.IsHomogeneous 4) (hd : g.IsWeightedHomogeneous id d)
    (hL : canonicalCOMLowerNat g=0) :
    natOccupationInner f (canonicalNatFourS4 g)=
      star (natOccupationInner (natFourPairRelativeSeed d) f)*
        natOccupationInner (natFourPairRelativeSeed d) g := by
  rw [natFourPairRelativeSeed_eq_marked]
  exact canonicalNatFourS4_relative_rank_form d f g hN hd hL

#print axioms natFour_s4_rotated_relative_word
#print axioms natFourPairRelativeSeed_eq_marked
#print axioms canonicalNatFourS4_pair_relative_rank_form
end TorusLean.BosonFiniteCertificate
