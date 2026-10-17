import torus.shared.ThermalCoherentJacobiFourRelative

/-! Particle and orbital degree of the concrete four-body marked insertion.
These are actual polynomial-support assertions, not domain assumptions. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace TorusLean.Shared.ThermalCoherentJacobiFourInsertion
open TorusLean.Boson TorusLean.BosonFiniteCertificate
open TorusLean.Shared.ThermalCoherentJacobiInsertion
open scoped BigOperators

private theorem spectatorScaled_homogeneous (j : ℕ) : (spectatorScaled j).IsHomogeneous 1 :=
  (MvPolynomial.homogeneousSubmodule ℕ ℂ 1).smul_mem _ (MvPolynomial.isHomogeneous_X ℂ j)

private theorem spectatorScaled_weighted (j : ℕ) :
    (spectatorScaled j).IsWeightedHomogeneous id j :=
  (MvPolynomial.weightedHomogeneousSubmodule ℂ id j).smul_mem _
    (MvPolynomial.isWeightedHomogeneous_X ℂ id j)

theorem pairRaised_bihomogeneous (p : ℕ) :
    (pairRaised p).IsHomogeneous 2 ∧ (pairRaised p).IsWeightedHomogeneous id p := by
  rw [pairRaised_binomial]
  constructor
  · apply (MvPolynomial.homogeneousSubmodule ℕ ℂ 2).smul_mem
    apply Submodule.sum_mem
    intro i hi
    rw [← Nat.cast_smul_eq_nsmul ℂ]
    exact (MvPolynomial.homogeneousSubmodule ℕ ℂ 2).smul_mem _
      ((spectatorScaled_homogeneous i).mul (spectatorScaled_homogeneous (p-i)))
  · apply (MvPolynomial.weightedHomogeneousSubmodule ℂ id p).smul_mem
    apply Submodule.sum_mem
    intro i hi
    rw [← Nat.cast_smul_eq_nsmul ℂ]
    apply Submodule.smul_mem
    have h := (spectatorScaled_weighted i).mul (spectatorScaled_weighted (p-i))
    apply (MvPolynomial.mem_weightedHomogeneousSubmodule ℂ id p _).mpr
    simpa only [Nat.add_sub_of_le (Nat.le_of_lt_succ (Finset.mem_range.mp hi))] using h

theorem markedFourBasisInsertion_bihomogeneous (p j m : ℕ) :
    (markedFourBasisInsertion p j m).IsHomogeneous 4 ∧
      (markedFourBasisInsertion p j m).IsWeightedHomogeneous id (p+j+m) := by
  obtain ⟨hN,hd⟩ := pairRaised_bihomogeneous p
  constructor
  · exact (MvPolynomial.homogeneousSubmodule ℕ ℂ 4).smul_mem _
      ((hN.mul (spectatorScaled_homogeneous j)).mul (spectatorScaled_homogeneous m))
  · exact (MvPolynomial.weightedHomogeneousSubmodule ℂ id (p+j+m)).smul_mem _
      ((hd.mul (spectatorScaled_weighted j)).mul (spectatorScaled_weighted m))

/-- Every marked homogeneous source has particle number four, and its marked
degree is exactly the actual orbital weighted degree after insertion. -/
theorem markedW4_homogeneous_bihomogeneous (d : ℕ) (f : MarkedFourOscillator)
    (hf : f.IsHomogeneous d) :
    (markedW4 f).IsHomogeneous 4 ∧ (markedW4 f).IsWeightedHomogeneous id d := by
  have hterm (n : Fin 3 →₀ ℕ) (hn : n ∈ f.support) : n 0+n 1+n 2=d := by
    have hdeg : n.degree=d := by
      by_contra h
      exact (MvPolynomial.mem_support_iff.mp hn) (hf.coeff_eq_zero h)
    simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_three, add_assoc] using hdeg
  rw [← MvPolynomial.support_sum_monomial_coeff f, map_sum]
  constructor
  · apply (MvPolynomial.homogeneousSubmodule ℕ ℂ 4).sum_mem
    intro n hn
    rw [markedW4_monomial]
    exact Submodule.smul_mem _ _ (markedFourBasisInsertion_bihomogeneous (n 0) (n 1) (n 2)).1
  · apply (MvPolynomial.weightedHomogeneousSubmodule ℂ id d).sum_mem
    intro n hn
    rw [markedW4_monomial]
    apply Submodule.smul_mem
    apply (MvPolynomial.mem_weightedHomogeneousSubmodule ℂ id d _).mpr
    simpa only [hterm n hn] using
      (markedFourBasisInsertion_bihomogeneous (n 0) (n 1) (n 2)).2

theorem spectatorDifference_homogeneous : spectatorDifference.IsHomogeneous 1 := by
  exact (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ 1).sub_mem
    (MvPolynomial.isHomogeneous_X ℂ 1) (MvPolynomial.isHomogeneous_X ℂ 2)

theorem pairSpectatorDifference_homogeneous : pairSpectatorDifference.IsHomogeneous 1 := by
  exact (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ 1).sub_mem
    ((MvPolynomial.homogeneousSubmodule (Fin 3) ℂ 1).sub_mem
      (MvPolynomial.isHomogeneous_X ℂ 0) (MvPolynomial.isHomogeneous_X ℂ 1))
    (MvPolynomial.isHomogeneous_X ℂ 2)

theorem w4RelativeSeed_bihomogeneous (d e : ℕ) :
    (w4RelativeSeed d e).IsHomogeneous 4 ∧
      (w4RelativeSeed d e).IsWeightedHomogeneous id (d+e) := by
  have h := markedW4_homogeneous_bihomogeneous (d+e)
    (spectatorDifference^d * pairSpectatorDifference^e)
    (by simpa only [one_mul] using
      (spectatorDifference_homogeneous.pow d).mul (pairSpectatorDifference_homogeneous.pow e))
  exact ⟨(MvPolynomial.homogeneousSubmodule ℕ ℂ 4).smul_mem _ h.1,
    (MvPolynomial.weightedHomogeneousSubmodule ℂ id (d+e)).smul_mem _ h.2⟩

end TorusLean.Shared.ThermalCoherentJacobiFourInsertion
