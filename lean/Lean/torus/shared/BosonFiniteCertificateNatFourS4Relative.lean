import torus.shared.BosonFiniteCertificateNatFourS4Rank
import torus.shared.ThermalCoherentNatFourHamiltonianRelative

/-! The pair-pair S4 source is identified with the zero spectator-difference
slice of the already proved marked four-particle rotation. This is a genuine
source identity with the two 1/sqrt(2) pair vacua kept, before restriction to
COM-lowering zero. It does not identify S4 with the full H4 rank family. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open TorusLean.Shared.ThermalCoherentJacobiFourInsertion
open TorusLean.Shared.ThermalCoherentNatFourHamiltonian
open scoped BigOperators

theorem natFour_marked_pair_product (p q : ℕ) :
    markedW4 ((MvPolynomial.X 0)^p*spectatorCOM^q)=pairRaised p*pairRaised q := by
  have hpow : spectatorCOM^q=∑ j ∈ Finset.range (q+1), q.choose j •
      ((MvPolynomial.X 1 : MarkedFourOscillator)^j*(MvPolynomial.X 2)^(q-j)) := by
    simpa only [spectatorCOM,nsmul_eq_mul,mul_comm] using
      (add_pow (MvPolynomial.X 1 : MarkedFourOscillator) (MvPolynomial.X 2) q)
  rw [hpow,Finset.mul_sum,map_sum,pairRaised_binomial q]
  simp only [mul_nsmul,map_nsmul,mul_smul_comm,Finset.mul_sum,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [←mul_assoc,markedW4_Xpowers]
  simp only [markedFourBasisInsertion,spectatorSymScalar,
    ←Nat.cast_smul_eq_nsmul ℂ,smul_mul_assoc,mul_smul_comm,smul_smul,mul_assoc]
  congr 1
  ring

theorem natFour_pair_product_eq_marked_level (p q : ℕ) :
    pairCOMSeed p*pairCOMSeed q=w4PairSpectatorLevel 0 p q := by
  rw [w4PairSpectatorLevel]
  simp only [pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one,one_mul]
  rw [natFour_marked_pair_product]
  simp only [pairCOMSeed,pairCOMScale,smul_mul_smul_comm,smul_smul]

/-- Exactly the ordered pair-product source cross trace, after the true
finite equal-charge rotation. No matrix or isometry of the physical image
is assumed. -/
theorem natFour_pair_product_finite_cross (d : ℕ)
    (F G : Core ℕ ℂ →ₗ[ℂ] ℂ) :
    (∑ p : Fin (d+1), star (F (pairCOMSeed p.val*pairCOMSeed (d-p.val)))*
      G (pairCOMSeed p.val*pairCOMSeed (d-p.val))) =
    ∑ n : Fin (d+1), star (F (normalizedFourCOMDescendant n.val (w4RelativeSeed 0 (d-n.val))))*
      G (normalizedFourCOMDescendant n.val (w4RelativeSeed 0 (d-n.val))) := by
  simpa only [natFour_pair_product_eq_marked_level] using w4_pair_COM_finite_cross 0 d F G

private def natFour_s4_relative_inner (f : Core ℕ ℂ) : Core ℕ ℂ →ₗ[ℂ] ℂ where
  toFun := natOccupationInner f
  map_add' := natOccupationInner_add_right f
  map_smul' := by
    intro c g
    simp only [natOccupationInner_smul_right,smul_eq_mul,RingHom.id_apply]

/-- The true S4 rank on every N4 degree-d relative polynomial is the
pair-pair seed w4RelativeSeed 0 d, derived from the original double-pair
source rather than inferred from the Hamiltonian's larger rank family. -/
theorem canonicalNatFourS4_relative_rank_form (d : ℕ) (f g : Core ℕ ℂ)
    (hN : g.IsHomogeneous 4) (hd : g.IsWeightedHomogeneous id d)
    (hL : canonicalCOMLowerNat g=0) :
    natOccupationInner f (canonicalNatFourS4 g)=
      star (natOccupationInner (w4RelativeSeed 0 d) f)*
        natOccupationInner (w4RelativeSeed 0 d) g := by
  let F := natFour_s4_relative_inner g
  let G := natFour_s4_relative_inner f
  have hQ (s : Core ℕ ℂ) : star (F s)*G s=
      star (natOccupationInner s f)*natOccupationInner s g := by
    change star (natOccupationInner g s)*natOccupationInner f s=_
    rw [natOccupationInner_conj_symm,←natOccupationInner_conj_symm s f]
    ring
  rw [canonicalNatFourS4_normalized_rank_form d f g hN hd,
    nat_pair_list_range_sum,←Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ p : Fin (d+1), star (F (pairCOMSeed p.val*pairCOMSeed (d-p.val)))*
        G (pairCOMSeed p.val*pairCOMSeed (d-p.val)) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact (hQ _).symm
    _ = ∑ n : Fin (d+1), star (F (normalizedFourCOMDescendant n.val (w4RelativeSeed 0 (d-n.val))))*
        G (normalizedFourCOMDescendant n.val (w4RelativeSeed 0 (d-n.val))) :=
      natFour_pair_product_finite_cross d F G
    _ = _ := by
      rw [Finset.sum_eq_single (0 : Fin (d+1))]
      · simpa [normalizedFourCOMDescendant] using hQ (w4RelativeSeed 0 d)
      · intro n hn hn0
        change star (natOccupationInner g _)*natOccupationInner f _=0
        rw [natOccupationInner_conj_symm,
          normalizedFourCOMDescendant_vacuum_inner n.val _ g hL
            (by intro h; apply hn0; exact Fin.ext h),zero_mul]
      · simp

#print axioms natFour_marked_pair_product
#print axioms natFour_pair_product_eq_marked_level
#print axioms natFour_pair_product_finite_cross
#print axioms canonicalNatFourS4_relative_rank_form
end TorusLean.BosonFiniteCertificate
