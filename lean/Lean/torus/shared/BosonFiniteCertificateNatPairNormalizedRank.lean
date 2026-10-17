import torus.shared.BosonFiniteCertificateNatPairRank
import torus.shared.ThermalCoherentJacobiPair

/-! Exact identification of the actual pair-H rank vectors with the original
normalized pair-COM/spectator insertion seeds. The multiplicity factorials,
ordered-pair double count, and the pair vacuum's 1/sqrt(2) are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open scoped BigOperators

theorem nat_pair_list_range_sum {A : Type*} [AddCommMonoid A] (n : ℕ) (F : ℕ → A) :
    ((List.range n).map F).sum=∑ i ∈ Finset.range n, F i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ,Finset.sum_range_succ,ih]

theorem canonicalPairCreatorNat_apply (p : ℕ) (f : Core ℕ ℂ) :
    canonicalPairCreatorNat p f=∑ i ∈ Finset.range (p+1),
      pairCoefficientNat p i • ((MvPolynomial.X i * MvPolynomial.X (p-i))*f) := by
  rw [canonicalPairCreatorNat,nat_linear_list_sum_apply,nat_pair_list_range_sum]
  simp only [LinearMap.smul_apply,LinearMap.comp_apply,create,LinearMap.mulLeft_apply,mul_assoc]

theorem canonicalPairCreatorNat_eq_mul (p : ℕ) (f : Core ℕ ℂ) :
    canonicalPairCreatorNat p f=canonicalPairCreatorNat p 1*f := by
  rw [canonicalPairCreatorNat_apply,canonicalPairCreatorNat_apply,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [mul_one,smul_mul_assoc]

def natPairNormalization (p : ℕ) : ℂ :=
  (p.factorial:ℂ) / ((Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ)) : ℂ) * (Real.sqrt (2:ℝ) : ℂ))

theorem natPairNormalization_real (p : ℕ) : star (natPairNormalization p)=natPairNormalization p := by
  simp [natPairNormalization]

theorem natPairNormalization_sq (p : ℕ) :
    (natPairNormalization p)^2=(p.factorial:ℂ)/(2:ℂ)^(p+1) := by
  have hA : (Real.sqrt ((2:ℝ)^p*(p.factorial:ℝ)) : ℂ)^2=
      (2:ℂ)^p*(p.factorial:ℂ) := by
    exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤2^p*(p.factorial:ℝ) by positivity)
  have hB : (Real.sqrt (2:ℝ) : ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hp : (p.factorial:ℂ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p)
  rw [natPairNormalization,div_pow,mul_pow,hA,hB,pow_succ]
  field_simp [hp] <;> ring

theorem nat_pair_choose_factorial_roots (p i : ℕ) (hi : i≤p) :
    (p.choose i:ℂ)*(factorialRootNat i*factorialRootNat (p-i)) =
      (p.factorial:ℂ)*pairCoefficientNat p i := by
  have hs (j : ℕ) : (factorialRootNat j)^2=(j.factorial:ℂ) := by
    unfold factorialRootNat
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg j.factorial)
  have hc : (p.choose i:ℂ)*(i.factorial:ℂ)*((p-i).factorial:ℂ)=(p.factorial:ℂ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  have hn := mul_ne_zero (factorialRootNat_ne_zero i) (factorialRootNat_ne_zero (p-i))
  rw [pairCoefficientNat,←div_eq_mul_inv]
  apply (eq_div_iff hn).mpr
  calc
    _ = (p.choose i:ℂ)*((factorialRootNat i)^2)*((factorialRootNat (p-i))^2) := by ring
    _ = _ := by rw [hs,hs,hc]

theorem pairCOMSeed_eq_canonical_creator (p : ℕ) :
    pairCOMSeed p=natPairNormalization p • canonicalPairCreatorNat p 1 := by
  rw [pairCOMSeed_binomial,canonicalPairCreatorNat_apply]
  simp only [Finset.smul_sum,mul_one]
  apply Finset.sum_congr rfl
  intro i hi
  rw [←Nat.cast_smul_eq_nsmul ℂ,smul_smul,smul_smul,smul_smul]
  congr 1
  rw [mul_assoc,nat_pair_choose_factorial_roots p i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))]
  unfold natPairNormalization
  ring

theorem pairCOMSeed_spectator_eq_rankSeed (p j : ℕ) :
    pairCOMSeed p * MvPolynomial.X j=natPairNormalization p • canonicalNatPairRankSeed p j := by
  rw [pairCOMSeed_eq_canonical_creator,smul_mul_assoc,canonicalNatPairRankSeed]
  congr 1
  exact (canonicalPairCreatorNat_eq_mul p (MvPolynomial.X j)).symm

theorem pairCOMSeed_spectator_rank (p j : ℕ) (f : Core ℕ ℂ) :
    natOccupationInner (pairCOMSeed p * MvPolynomial.X j) f •
      (pairCOMSeed p * MvPolynomial.X j) =
    ((p.factorial:ℂ)/(2:ℂ)^(p+1)) •
      (natOccupationInner (canonicalNatPairRankSeed p j) f • canonicalNatPairRankSeed p j) := by
  rw [pairCOMSeed_spectator_eq_rankSeed,natOccupationInner_smul_left,
    natPairNormalization_real,smul_smul,smul_smul,←natPairNormalization_sq]
  congr 1
  ring

/-- The actual global Nat Hamiltonian on any N3 degree-d polynomial equals
the original normalized pair-COM/spectator rank sum, at every finite d. -/
theorem canonicalPairHamiltonianNat_normalized_rank_action (d : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id d) :
    canonicalPairHamiltonianNat f =
      ((List.range (d+1)).map fun p =>
        natOccupationInner (pairCOMSeed p * MvPolynomial.X (d-p)) f •
          (pairCOMSeed p * MvPolynomial.X (d-p))).sum := by
  rw [canonicalPairHamiltonianNat_rank_action d f hN hd]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  exact (pairCOMSeed_spectator_rank p (d-p) f).symm

theorem canonicalPairHamiltonianNat_normalized_rank_form (d : ℕ) (f g : Core ℕ ℂ)
    (hN : g.IsHomogeneous 3) (hd : g.IsWeightedHomogeneous id d) :
    natOccupationInner f (canonicalPairHamiltonianNat g) =
      ((List.range (d+1)).map fun p =>
        star (natOccupationInner (pairCOMSeed p * MvPolynomial.X (d-p)) f) *
          natOccupationInner (pairCOMSeed p * MvPolynomial.X (d-p)) g).sum := by
  rw [canonicalPairHamiltonianNat_normalized_rank_action d g hN hd,natOccupationInner_list_sum_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [natOccupationInner_smul_right,natOccupationInner_conj_symm,mul_comm]

#print axioms pairCOMSeed_eq_canonical_creator
#print axioms canonicalPairHamiltonianNat_normalized_rank_action
#print axioms canonicalPairHamiltonianNat_normalized_rank_form
end TorusLean.BosonFiniteCertificate
