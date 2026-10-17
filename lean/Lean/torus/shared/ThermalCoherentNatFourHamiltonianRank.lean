import torus.shared.ThermalCoherentNatFourHamiltonianTwoParseval
import torus.shared.BosonFiniteCertificateNatPairNormalizedRank
import torus.shared.ThermalCoherentJacobiFourInsertion

/-! Genuine all-Nat N4 pair-Hamiltonian resolution through the original
normalized pair-COM and ordered symmetric-spectator insertion vectors. The
Hamiltonian is the previously defined locally finite differential operator;
its action is derived from true N2 output Parseval and creator adjoints. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.Shared.ThermalCoherentNatFourHamiltonian
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Shared.ThermalCoherentJacobiFourInsertion
open scoped BigOperators

/-- Pair COM p and two original ordered spectator orbitals. The unique
spectator 1/sqrt(2) is independent of the normalized pair vacuum. -/
def w4PairCOMSeed (p j m : ℕ) : Core ℕ ℂ :=
  spectatorSymScalar • (pairCOMSeed p * MvPolynomial.X j * MvPolynomial.X m)

theorem w4PairCOMSeed_zero (j m : ℕ) : w4PairCOMSeed 0 j m=w4Seed j m := by
  simp [w4PairCOMSeed,w4Seed,pairCOMSeed,pairRaised_zero]

private theorem double_annihilate_four_output (a b D : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id D) :
    (annihilate b (annihilate a f)).IsHomogeneous 2 ∧
      (annihilate b (annihilate a f)).IsWeightedHomogeneous id (D-(a+b)) := by
  have hc (n : ℕ →₀ ℕ) (hn : (annihilate b (annihilate a f)).coeff n≠0) :
      f.coeff ((n+Finsupp.single b 1)+Finsupp.single a 1)≠0 := by
    intro hz
    apply hn
    change (MvPolynomial.pderiv b (MvPolynomial.pderiv a f)).coeff n=0
    simp only [MvPolynomial.coeff_pderiv,hz,zero_mul]
  constructor
  · intro n hn
    have h := hN (hc n hn)
    simp only [map_add,Finsupp.weight_single,Pi.one_apply,one_smul] at h
    change Finsupp.weight (1 : ℕ → ℕ) n=2
    omega
  · intro n hn
    have h := hd (hc n hn)
    simp only [map_add,Finsupp.weight_single,id_eq,one_smul] at h
    omega

/-- The actual pair remover has a genuine two-particle output of residual
orbital degree D-p. No source occupation table is supplied. -/
theorem canonicalPairNat_four_output (p D : ℕ) (hp : p≤D) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id D) :
    (canonicalPairNat p f).IsHomogeneous 2 ∧
      (canonicalPairNat p f).IsWeightedHomogeneous id (D-p) := by
  simp only [canonicalPairNat,nat_linear_list_sum_apply,nat_pair_list_range_sum,
    LinearMap.sum_apply,LinearMap.smul_apply,LinearMap.comp_apply]
  constructor
  · apply (MvPolynomial.homogeneousSubmodule ℕ ℂ 2).sum_mem
    intro a ha
    exact Submodule.smul_mem _ _ (double_annihilate_four_output a (p-a) D f hN hd).1
  · apply (MvPolynomial.weightedHomogeneousSubmodule ℂ id (D-p)).sum_mem
    intro a ha
    apply Submodule.smul_mem
    apply (MvPolynomial.mem_weightedHomogeneousSubmodule ℂ id (D-p) _).mpr
    have hh := (double_annihilate_four_output a (p-a) D f hN hd).2
    simpa only [Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp ha))] using hh

theorem w4PairCOMSeed_eq_creator (p j m : ℕ) :
    w4PairCOMSeed p j m = (spectatorSymScalar*natPairNormalization p) •
      canonicalPairCreatorNat p (MvPolynomial.X j*MvPolynomial.X m) := by
  rw [w4PairCOMSeed,pairCOMSeed_eq_canonical_creator,smul_mul_assoc,smul_mul_assoc,
    smul_smul,canonicalPairCreatorNat_eq_mul p (MvPolynomial.X j*MvPolynomial.X m),mul_assoc]

private theorem spectatorSymScalar_real : star spectatorSymScalar=spectatorSymScalar := by
  simp [spectatorSymScalar]

private theorem spectatorSymScalar_sq : spectatorSymScalar^2=(1/2:ℂ) := by
  have hs : (Real.sqrt (2:ℝ):ℂ)^2=2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  rw [spectatorSymScalar,inv_pow,hs]
  norm_num

/-- Exact rank coefficient, including the ordered N2 Parseval half. -/
theorem w4PairCOMSeed_rank (p j m : ℕ) (f : Core ℕ ℂ) :
    natOccupationInner (w4PairCOMSeed p j m) f • w4PairCOMSeed p j m =
      (((p.factorial:ℂ)/(2:ℂ)^(p+1))/2) •
        (natOccupationInner (canonicalPairCreatorNat p (MvPolynomial.X j*MvPolynomial.X m)) f •
          canonicalPairCreatorNat p (MvPolynomial.X j*MvPolynomial.X m)) := by
  rw [w4PairCOMSeed_eq_creator,natOccupationInner_smul_left,star_mul,
    spectatorSymScalar_real,natPairNormalization_real,smul_smul,smul_smul]
  congr 1
  calc
    _ = spectatorSymScalar^2*(natPairNormalization p)^2*
        natOccupationInner (canonicalPairCreatorNat p (MvPolynomial.X j*MvPolynomial.X m)) f := by ring
    _ = _ := by rw [spectatorSymScalar_sq,natPairNormalization_sq]; ring

private theorem canonicalPairNat_four_ordered_rank (p D : ℕ) (hp : p≤D) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id D) :
    canonicalPairCreatorNat p (canonicalPairNat p f) = (1/2:ℂ) •
      ∑ j ∈ Finset.range (D-p+1),
        natOccupationInner (canonicalPairCreatorNat p (MvPolynomial.X j*MvPolynomial.X (D-p-j))) f •
          canonicalPairCreatorNat p (MvPolynomial.X j*MvPolynomial.X (D-p-j)) := by
  have hh := canonicalPairNat_four_output p D hp f hN hd
  rw [nat_two_ordered_parseval (D-p) (canonicalPairNat p f) hh.1 hh.2,
    map_smul,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_smul,canonicalPairCreatorNat_adjoint]

/-- The original global Nat Hamiltonian, restricted by genuine particle and
orbital homogeneity only, is the complete ordered insertion rank sum. -/
theorem canonicalPairHamiltonianNat_four_rank_action (D : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id D) :
    canonicalPairHamiltonianNat f = ∑ p ∈ Finset.range (D+1),
      ∑ j ∈ Finset.range (D-p+1),
        natOccupationInner (w4PairCOMSeed p j (D-p-j)) f • w4PairCOMSeed p j (D-p-j) := by
  rw [canonicalPairHamiltonianNat_eq_cutoff_weighted D f hd,
    canonicalPairHamiltonianNatCutoff,nat_linear_list_sum_apply,nat_pair_list_range_sum]
  simp only [LinearMap.smul_apply,LinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro p hp
  rw [canonicalPairNat_four_ordered_rank p D (Nat.le_of_lt_succ (Finset.mem_range.mp hp)) f hN hd]
  simp only [Finset.smul_sum,smul_smul]
  apply Finset.sum_congr rfl
  intro j hj
  rw [w4PairCOMSeed_rank]
  simp only [smul_smul]
  congr 1
  ring

theorem canonicalPairHamiltonianNat_four_rank_form (D : ℕ) (f g : Core ℕ ℂ)
    (hN : g.IsHomogeneous 4) (hd : g.IsWeightedHomogeneous id D) :
    natOccupationInner f (canonicalPairHamiltonianNat g) =
      ∑ p ∈ Finset.range (D+1), ∑ j ∈ Finset.range (D-p+1),
        star (natOccupationInner (w4PairCOMSeed p j (D-p-j)) f)*
          natOccupationInner (w4PairCOMSeed p j (D-p-j)) g := by
  rw [canonicalPairHamiltonianNat_four_rank_action D g hN hd,natOccupationInner_sum_right]
  apply Finset.sum_congr rfl
  intro p hp
  rw [natOccupationInner_sum_right]
  apply Finset.sum_congr rfl
  intro j hj
  rw [natOccupationInner_smul_right,natOccupationInner_conj_symm]
  ring

end TorusLean.Shared.ThermalCoherentNatFourHamiltonian
