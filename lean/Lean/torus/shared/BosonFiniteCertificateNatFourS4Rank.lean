import torus.shared.BosonFiniteCertificateNatFourS4AmplitudeCore
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! The actual double-pair S4 source resolves into normalized pair-COM
product seeds on the complete Nat N4 sector. Both original pair halves are
retained through natPairNormalization_sq. These are S4 seeds, not the
single-pair Hamiltonian's two-spectator relative seeds. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open scoped BigOperators

private theorem natFour_pair_particle (p N : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous (N+2)) : (canonicalPairNat p f).IsHomogeneous N := by
  rw [canonicalPairNat,nat_linear_list_sum_apply,nat_pair_list_range_sum]
  apply (MvPolynomial.homogeneousSubmodule ℕ ℂ N).sum_mem
  intro a ha
  simp only [LinearMap.smul_apply,LinearMap.comp_apply]
  apply (MvPolynomial.homogeneousSubmodule ℕ ℂ N).smul_mem
  change (MvPolynomial.pderiv (p-a) (MvPolynomial.pderiv a f)).IsHomogeneous N
  have hd : N+2-1-1=N := by omega
  simpa only [hd] using (hN.pderiv (i := a)).pderiv (i := p-a)

theorem canonicalNatFourDoublePair_homogeneous_zero (p q : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) : (canonicalNatFourDoublePair p q f).IsHomogeneous 0 :=
  natFour_pair_particle q 0 (canonicalPairNat p f) (natFour_pair_particle p 2 f hN)

private theorem natFour_s4_inner_one (f : Core ℕ ℂ) : natOccupationInner 1 f=f.coeff 0 := by
  change natOccupationInner (MvPolynomial.monomial 0 1) f = _
  rw [natOccupationInner_monomial_left]
  simp [natOccupationWeight,Finsupp.prod]

theorem canonicalNatFourDoublePair_vacuum (p q : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) :
    canonicalNatFourDoublePair p q f=
      natOccupationInner (canonicalNatFourDoubleCreator p q 1) f • (1 : Core ℕ ℂ) := by
  have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp
    ((MvPolynomial.totalDegree_zero_iff_isHomogeneous ℕ).mpr
      (canonicalNatFourDoublePair_homogeneous_zero p q f hN))
  have hi := canonicalNatFourDoubleCreator_adjoint p q 1 f
  rw [natFour_s4_inner_one] at hi
  rw [hc,←hi]
  simp only [Algebra.smul_def,mul_one,MvPolynomial.algebraMap_eq]

theorem natFourPairCOM_product_eq_creator (p q : ℕ) :
    pairCOMSeed p*pairCOMSeed q=(natPairNormalization p*natPairNormalization q) •
      canonicalNatFourDoubleCreator p q 1 := by
  rw [pairCOMSeed_eq_canonical_creator,pairCOMSeed_eq_canonical_creator,
    smul_mul_smul_comm,canonicalNatFourDoubleCreator,LinearMap.comp_apply,
    canonicalPairCreatorNat_eq_mul p (canonicalPairCreatorNat q 1)]

theorem natFourPairCOM_product_rank (p q : ℕ) (f : Core ℕ ℂ) :
    natOccupationInner (pairCOMSeed p*pairCOMSeed q) f • (pairCOMSeed p*pairCOMSeed q)=
      (natFourPairWeight p q : ℂ) •
        (natOccupationInner (canonicalNatFourDoubleCreator p q 1) f •
          canonicalNatFourDoubleCreator p q 1) := by
  rw [natFourPairCOM_product_eq_creator,natOccupationInner_smul_left]
  simp only [star_mul,natPairNormalization_real,smul_smul]
  have hw : (natFourPairWeight p q : ℂ)=natPairNormalization p^2*natPairNormalization q^2 := by
    rw [natPairNormalization_sq,natPairNormalization_sq]
    simp only [natFourPairWeight,Rat.cast_mul,Rat.cast_div,Rat.cast_natCast,Rat.cast_pow,
      Rat.cast_ofNat]
  rw [hw]
  congr 1
  ring

theorem canonicalNatFourS4_normalized_rank_action (d : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id d) :
    canonicalNatFourS4 f=((List.range (d+1)).map fun p =>
      natOccupationInner (pairCOMSeed p*pairCOMSeed (d-p)) f •
        (pairCOMSeed p*pairCOMSeed (d-p))).sum := by
  rw [canonicalNatFourS4_eq_shell_four d f hN hd,
    canonicalNatFourS4Shell,nat_linear_list_sum_apply]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [LinearMap.smul_apply,LinearMap.comp_apply]
  rw [canonicalNatFourDoublePair_vacuum p (d-p) f hN,map_smul]
  exact (natFourPairCOM_product_rank p (d-p) f).symm

theorem canonicalNatFourS4_normalized_rank_form (d : ℕ) (f g : Core ℕ ℂ)
    (hN : g.IsHomogeneous 4) (hd : g.IsWeightedHomogeneous id d) :
    natOccupationInner f (canonicalNatFourS4 g)=
      ((List.range (d+1)).map fun p =>
        star (natOccupationInner (pairCOMSeed p*pairCOMSeed (d-p)) f)*
          natOccupationInner (pairCOMSeed p*pairCOMSeed (d-p)) g).sum := by
  rw [canonicalNatFourS4_normalized_rank_action d g hN hd,natOccupationInner_list_sum_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  simp only [natOccupationInner_smul_right,natOccupationInner_conj_symm,mul_comm]

#print axioms canonicalNatFourDoublePair_homogeneous_zero
#print axioms canonicalNatFourDoublePair_vacuum
#print axioms natFourPairCOM_product_eq_creator
#print axioms natFourPairCOM_product_rank
#print axioms canonicalNatFourS4_normalized_rank_action
#print axioms canonicalNatFourS4_normalized_rank_form
end TorusLean.BosonFiniteCertificate
