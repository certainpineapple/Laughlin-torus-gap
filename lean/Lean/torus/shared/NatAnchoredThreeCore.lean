import torus.shared.BosonFiniteCertificateNatRelativeSeedNorm

/-! The original anchored bosonic operator on the actual Nat polynomial core.
A0 is one half of the genuine zero-pair creator/remover composition; K is
A0 composed with H-I. Neither is defined through a relative compression. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Shared.BosonFiniteCertificateConjugation
open scoped BigOperators

def natAnchoredThreeA0 : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  (1/2:ℂ) • (canonicalPairCreatorNat 0).comp (canonicalPairNat 0)

def natAnchoredThreeK : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  natAnchoredThreeA0.comp (canonicalPairHamiltonianNat - LinearMap.id)

def natAnchoredThreeKet (l : ℕ) : Core ℕ ℂ := w3Seed l

def natAnchoredThreeBra (l : ℕ) : Core ℕ ℂ := pairCOMSeed l * MvPolynomial.X 0

def natAnchoredThreeDecay (l : ℕ) : ℂ := ((Real.sqrt (2:ℝ):ℂ)^l)⁻¹

theorem natAnchoredThreePair_zero :
    canonicalPairNat 0 = (annihilate 0).comp (annihilate 0) := by
  simp [canonicalPairNat,pairCoefficientNat,factorialRootNat]

theorem natAnchoredThreeCreator_zero :
    canonicalPairCreatorNat 0 = (create 0).comp (create 0) := by
  simp [canonicalPairCreatorNat,pairCoefficientNat,factorialRootNat]

theorem natAnchoredThreeA0_apply (f : Core ℕ ℂ) :
    natAnchoredThreeA0 f = (1/2:ℂ) •
      ((MvPolynomial.X 0)^2 * MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 f)) := by
  simp only [natAnchoredThreeA0,LinearMap.smul_apply,LinearMap.comp_apply,
    natAnchoredThreePair_zero,natAnchoredThreeCreator_zero,create,annihilate,
    LinearMap.mulLeft_apply,LinearMap.comp_apply,Derivation.coeFn_coe,pow_two,mul_assoc]

theorem natAnchoredThree_pairCOM_zero : pairCOMSeed 0 = pairVacuum := by
  simp [pairCOMSeed,pairRaised_zero]

theorem natAnchoredThree_pairSpectator_mem (p j : ℕ) :
    pairCOMSeed p * MvPolynomial.X j ∈ threeWordDegreeSpanNat (p+j) := by
  rw [pairCOMSeed_spectator_eq_marked]
  exact Submodule.smul_mem _ _ (markedBasisInsertion_mem p j)

theorem natAnchoredThreeKet_bihomogeneous (l : ℕ) :
    (natAnchoredThreeKet l).IsHomogeneous 3 ∧
      (natAnchoredThreeKet l).IsWeightedHomogeneous id l := by
  apply threeWordDegreeSpanNat_bihomogeneous l
  simpa only [natAnchoredThree_pairCOM_zero,natAnchoredThreeKet,w3Seed,Nat.zero_add]
    using natAnchoredThree_pairSpectator_mem 0 l

theorem natAnchoredThreeBra_bihomogeneous (l : ℕ) :
    (natAnchoredThreeBra l).IsHomogeneous 3 ∧
      (natAnchoredThreeBra l).IsWeightedHomogeneous id l := by
  apply threeWordDegreeSpanNat_bihomogeneous l
  simpa only [natAnchoredThreeBra,Nat.add_zero] using natAnchoredThree_pairSpectator_mem l 0

/-- No l>0 restriction: at l=0 the ket has occupation norm squared three. -/
theorem natAnchoredThreeA0_rank (l : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id l) :
    natAnchoredThreeA0 f =
      natOccupationInner (natAnchoredThreeKet l) f • natAnchoredThreeKet l := by
  rw [natAnchoredThreeA0,LinearMap.smul_apply,LinearMap.comp_apply,
    canonicalPairNat_rank_action 0 l f hN hd,Nat.sub_zero]
  simpa only [Nat.factorial_zero,Nat.cast_one,Nat.zero_add,pow_one,natAnchoredThree_pairCOM_zero,
    natAnchoredThreeKet,w3Seed] using (pairCOMSeed_spectator_rank 0 l f).symm

/-- The genuine H preserves the full N3 orbital block, not only its relative part. -/
theorem natAnchoredThree_H_bihomogeneous (l : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id l) :
    (canonicalPairHamiltonianNat f).IsHomogeneous 3 ∧
      (canonicalPairHamiltonianNat f).IsWeightedHomogeneous id l := by
  apply threeWordDegreeSpanNat_bihomogeneous l
  rw [canonicalPairHamiltonianNat_normalized_rank_action l f hN hd,nat_pair_list_range_sum]
  apply Submodule.sum_mem
  intro p hp
  apply Submodule.smul_mem
  have he : p+(l-p)=l := Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hp))
  simpa only [he] using natAnchoredThree_pairSpectator_mem p (l-p)

theorem natAnchoredThree_H_adjoint (l : ℕ) (f g : Core ℕ ℂ)
    (hNf : f.IsHomogeneous 3) (hdf : f.IsWeightedHomogeneous id l)
    (hNg : g.IsHomogeneous 3) (hdg : g.IsWeightedHomogeneous id l) :
    natOccupationInner f (canonicalPairHamiltonianNat g) =
      natOccupationInner (canonicalPairHamiltonianNat f) g := by
  rw [canonicalPairHamiltonianNat_normalized_rank_action l g hNg hdg,
    canonicalPairHamiltonianNat_normalized_rank_action l f hNf hdf,
    natOccupationInner_list_sum_left,natOccupationInner_list_sum_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [natOccupationInner_smul_left,natOccupationInner_smul_right,
    natOccupationInner_conj_symm,mul_comm]

theorem natAnchoredThree_inner_sub_left (f g h : Core ℕ ℂ) :
    natOccupationInner (f-g) h = natOccupationInner f h - natOccupationInner g h := by
  rw [sub_eq_add_neg,show -g=(-1:ℂ) • g by simp,
    natOccupationInner_add_left,natOccupationInner_smul_left]
  simp [sub_eq_add_neg]

theorem natAnchoredThree_inner_sub_right (f g h : Core ℕ ℂ) :
    natOccupationInner f (g-h) = natOccupationInner f g - natOccupationInner f h := by
  rw [sub_eq_add_neg,show -h=(-1:ℂ) • h by simp,
    natOccupationInner_add_right,natOccupationInner_smul_right]
  simp [sub_eq_add_neg]

/-- The bra of the actual anchored operator is (H-I)q, with H moved only by
its proved occupation adjoint on the genuine full degree block. -/
theorem natAnchoredThreeK_rank_pre (l : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 3) (hd : f.IsWeightedHomogeneous id l) :
    natAnchoredThreeK f =
      natOccupationInner
        (canonicalPairHamiltonianNat (natAnchoredThreeKet l)-natAnchoredThreeKet l) f •
          natAnchoredThreeKet l := by
  have hH := natAnchoredThree_H_bihomogeneous l f hN hd
  rw [natAnchoredThreeK,LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,
    natAnchoredThreeA0_rank l _ (hH.1.sub hN) (hH.2.sub hd),
    natAnchoredThree_inner_sub_right,natAnchoredThree_inner_sub_left,
    natAnchoredThree_H_adjoint l (natAnchoredThreeKet l) f
      (natAnchoredThreeKet_bihomogeneous l).1 (natAnchoredThreeKet_bihomogeneous l).2 hN hd]

#print axioms natAnchoredThreePair_zero
#print axioms natAnchoredThreeCreator_zero
#print axioms natAnchoredThreeA0_apply
#print axioms natAnchoredThree_pairCOM_zero
#print axioms natAnchoredThree_pairSpectator_mem
#print axioms natAnchoredThreeKet_bihomogeneous
#print axioms natAnchoredThreeBra_bihomogeneous
#print axioms natAnchoredThreeA0_rank
#print axioms natAnchoredThree_H_bihomogeneous
#print axioms natAnchoredThree_H_adjoint
#print axioms natAnchoredThree_inner_sub_left
#print axioms natAnchoredThree_inner_sub_right
#print axioms natAnchoredThreeK_rank_pre
end TorusLean.BosonFiniteCertificate
