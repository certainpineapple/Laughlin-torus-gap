import torus.shared.ThermalCoherentNatFourHamiltonianPairRotation
import torus.shared.BosonFiniteCertificateNatCOMOccupationAdjoint
import Mathlib.Algebra.BigOperators.Intervals

/-! Full relative multiplicity resolution of the original Nat N4 Hamiltonian.
Two actual finite source rotations preserve the complete ordered rank sum.
The genuine COM occupation adjoint then kills all positive COM descendants
against a true relative vacuum. No orthonormality, nonzero, spanning, or
Hamiltonian-invariance premise is placed on the inserted relative images. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.Shared.ThermalCoherentNatFourHamiltonian
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.ThermalCoherentJacobiFourInsertion
open scoped BigOperators ComplexConjugate

private theorem natFour_triangle_swap (D : ℕ) (F : ℕ → ℕ → ℂ) :
    (∑ p ∈ Finset.range (D+1), ∑ d ∈ Finset.range (D-p+1), F p d) =
      ∑ d ∈ Finset.range (D+1), ∑ p ∈ Finset.range (D-d+1), F p d := by
  have hi (G : ℕ → ℂ) (p : ℕ) (hp : p ∈ Finset.range (D+1)) :
      (∑ d ∈ Finset.range (D-p+1), G d) =
        ∑ d ∈ Finset.range (D+1), if p+d≤D then G d else 0 := by
    rw [←Finset.sum_filter]
    congr 1
    ext d
    simp only [Finset.mem_range,Finset.mem_filter]
    have hp' := Finset.mem_range.mp hp
    omega
  calc
    _ = ∑ p ∈ Finset.range (D+1), ∑ d ∈ Finset.range (D+1),
        if p+d≤D then F p d else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hi (F p) p hp
    _ = ∑ d ∈ Finset.range (D+1), ∑ p ∈ Finset.range (D+1),
        if p+d≤D then F p d else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      simpa only [Nat.add_comm] using (hi (fun p => F p d) d hd).symm

/-- Both genuine finite source rotations, before any COM vacuum restriction. -/
theorem w4_two_rotations_finite_cross (D : ℕ) (F G : Core ℕ ℂ →ₗ[ℂ] ℂ) :
    (∑ p ∈ Finset.range (D+1), ∑ j ∈ Finset.range (D-p+1),
      star (F (w4PairCOMSeed p j (D-p-j)))*G (w4PairCOMSeed p j (D-p-j))) =
    ∑ d ∈ Finset.range (D+1), ∑ n ∈ Finset.range (D-d+1),
      star (F (normalizedFourCOMDescendant n (w4RelativeSeed d (D-d-n))))*
        G (normalizedFourCOMDescendant n (w4RelativeSeed d (D-d-n))) := by
  let Q (s : Core ℕ ℂ) := star (F s)*G s
  have hfirst (p : ℕ) :
      (∑ j ∈ Finset.range (D-p+1), Q (w4PairCOMSeed p j (D-p-j))) =
        ∑ d ∈ Finset.range (D-p+1), Q (w4PairSpectatorLevel d p (D-p-d)) := by
    have h := w4_pair_spectator_finite_cross p (D-p) F G
    let A : ℕ → ℂ := fun j => Q (w4PairCOMSeed p j (D-p-j))
    let B : ℕ → ℂ := fun l => Q (w4PairSpectatorLevel (D-p-l) p l)
    change (∑ j : Fin (D-p+1), A j.val) = ∑ l : Fin (D-p+1), B l.val at h
    rw [Fin.sum_univ_eq_sum_range,Fin.sum_univ_eq_sum_range] at h
    calc
      _ = ∑ l ∈ Finset.range (D-p+1), Q (w4PairSpectatorLevel (D-p-l) p l) := h
      _ = _ := by
        conv_rhs => rw [←Finset.sum_range_reflect
          (fun d => Q (w4PairSpectatorLevel d p (D-p-d))) (D-p+1)]
        apply Finset.sum_congr rfl
        intro l hl
        have hl' := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
        rw [show D-p+1-1-l=D-p-l by omega,Nat.sub_sub_self hl']
  change (∑ p ∈ Finset.range (D+1), ∑ j ∈ Finset.range (D-p+1), Q (w4PairCOMSeed p j (D-p-j))) =
    ∑ d ∈ Finset.range (D+1), ∑ n ∈ Finset.range (D-d+1),
      Q (normalizedFourCOMDescendant n (w4RelativeSeed d (D-d-n)))
  calc
    _ = ∑ p ∈ Finset.range (D+1), ∑ d ∈ Finset.range (D-p+1),
        Q (w4PairSpectatorLevel d p (D-p-d)) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact hfirst p
    _ = ∑ d ∈ Finset.range (D+1), ∑ p ∈ Finset.range (D-d+1),
        Q (w4PairSpectatorLevel d p (D-p-d)) := natFour_triangle_swap D _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      calc
        _ = ∑ p ∈ Finset.range (D-d+1), Q (w4PairSpectatorLevel d p (D-d-p)) := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [show D-p-d=D-d-p by omega]
        _ = _ := by
          have h := w4_pair_COM_finite_cross d (D-d) F G
          let A : ℕ → ℂ := fun p => Q (w4PairSpectatorLevel d p (D-d-p))
          let B : ℕ → ℂ := fun n => Q (normalizedFourCOMDescendant n (w4RelativeSeed d (D-d-n)))
          change (∑ p : Fin (D-d+1), A p.val) = ∑ n : Fin (D-d+1), B n.val at h
          rw [Fin.sum_univ_eq_sum_range,Fin.sum_univ_eq_sum_range] at h
          exact h

/-- Positive COM levels pair to zero with every genuine relative vacuum. -/
theorem normalizedFourCOMDescendant_vacuum_inner (n : ℕ) (r f : Core ℕ ℂ)
    (hL : canonicalCOMLowerNat f=0) (hn : n≠0) :
    natOccupationInner (normalizedFourCOMDescendant n r) f=0 := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [normalizedFourCOMDescendant,natOccupationInner_smul_left,
    canonicalCOMRaiseNat_iterate_orthogonal_of_lower_eq_zero n r f hL,mul_zero]

private def natFourInnerFunctional (f : Core ℕ ℂ) : Core ℕ ℂ →ₗ[ℂ] ℂ where
  toFun := natOccupationInner f
  map_add' := natOccupationInner_add_right f
  map_smul' := by
    intro c g
    simp only [natOccupationInner_smul_right,smul_eq_mul,RingHom.id_apply]

/-- The true planar N4 Hamiltonian cross form on every relative polynomial,
including every physical multiplicity in orbital degree D. -/
theorem canonicalPairHamiltonianNat_four_relative_rank_form (D : ℕ) (f g : Core ℕ ℂ)
    (hN : g.IsHomogeneous 4) (hd : g.IsWeightedHomogeneous id D)
    (hL : canonicalCOMLowerNat g=0) :
    natOccupationInner f (canonicalPairHamiltonianNat g) =
      ∑ d ∈ Finset.range (D+1), star (natOccupationInner (w4RelativeSeed d (D-d)) f)*
        natOccupationInner (w4RelativeSeed d (D-d)) g := by
  let F := natFourInnerFunctional g
  let G := natFourInnerFunctional f
  have hQ (s : Core ℕ ℂ) : star (F s)*G s =
      star (natOccupationInner s f)*natOccupationInner s g := by
    change star (natOccupationInner g s)*natOccupationInner f s = _
    rw [natOccupationInner_conj_symm,←natOccupationInner_conj_symm s f]
    ring
  rw [canonicalPairHamiltonianNat_four_rank_form D f g hN hd]
  calc
    _ = ∑ p ∈ Finset.range (D+1), ∑ j ∈ Finset.range (D-p+1),
        star (F (w4PairCOMSeed p j (D-p-j)))*G (w4PairCOMSeed p j (D-p-j)) := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro j hj
      exact (hQ _).symm
    _ = ∑ d ∈ Finset.range (D+1), ∑ n ∈ Finset.range (D-d+1),
        star (F (normalizedFourCOMDescendant n (w4RelativeSeed d (D-d-n))))*
          G (normalizedFourCOMDescendant n (w4RelativeSeed d (D-d-n))) :=
      w4_two_rotations_finite_cross D F G
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd'
      rw [Finset.sum_eq_single 0]
      · simpa [normalizedFourCOMDescendant] using hQ (w4RelativeSeed d (D-d))
      · intro n hn hn0
        change star (natOccupationInner g _)*natOccupationInner f _=0
        rw [natOccupationInner_conj_symm,
          normalizedFourCOMDescendant_vacuum_inner n _ g hL hn0,zero_mul]
      · simp

/-- Full core action identity, obtained from the actual cross form and the
positive factorial monomial coefficients, not from a compressed definition. -/
theorem canonicalPairHamiltonianNat_four_relative_rank_action (D : ℕ) (f : Core ℕ ℂ)
    (hN : f.IsHomogeneous 4) (hd : f.IsWeightedHomogeneous id D)
    (hL : canonicalCOMLowerNat f=0) :
    canonicalPairHamiltonianNat f = ∑ d ∈ Finset.range (D+1),
      natOccupationInner (w4RelativeSeed d (D-d)) f • w4RelativeSeed d (D-d) := by
  apply MvPolynomial.ext
  intro n
  have h := canonicalPairHamiltonianNat_four_relative_rank_form D (MvPolynomial.monomial n 1) f hN hd hL
  have hr : natOccupationInner (MvPolynomial.monomial n 1)
      (∑ d ∈ Finset.range (D+1), natOccupationInner (w4RelativeSeed d (D-d)) f • w4RelativeSeed d (D-d)) =
      ∑ d ∈ Finset.range (D+1), star (natOccupationInner (w4RelativeSeed d (D-d))
        (MvPolynomial.monomial n 1))*natOccupationInner (w4RelativeSeed d (D-d)) f := by
    rw [natOccupationInner_sum_right]
    apply Finset.sum_congr rfl
    intro d hd'
    rw [natOccupationInner_smul_right,natOccupationInner_conj_symm]
    ring
  rw [←hr] at h
  simp only [natOccupationInner_monomial_left,star_one,mul_one] at h
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (ne_of_gt (natOccupationWeight_pos n))) h

end TorusLean.Shared.ThermalCoherentNatFourHamiltonian
