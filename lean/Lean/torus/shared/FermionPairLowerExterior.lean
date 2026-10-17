import torus.shared.FermionPairLowerCoefficients
import torus.shared.ThermalCoherentFermionCOMRelativeSource

/-! Total lowering of the original unordered m=1 pair.  The only boundary
term discarded is a literal repeated-generator exterior square. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionCOMWords
open TorusLean.Shared.FermionRelativeFrame
open TorusLean.Shared.FermionLocalJet TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.ThermalCoherentFermionAnchored
open TorusLean.Shared.ThermalCoherentFermionJetWord
open scoped BigOperators

private theorem pair_lower_coefficient_lt (p i j : ℕ) (hij : i+j=p+1) (hlt : i<j) :
    pairLeftCoefficient (p+1) (i+1) * Real.sqrt (i+1:ℝ) +
      pairLeftCoefficient (p+1) i * Real.sqrt (j+1:ℝ) =
        Real.sqrt (2*(p+1:ℝ)) * pairLeftCoefficient p i := by
  have h1 : p+1+1-(i+1)=j := by omega
  have h2 : p+1+1-i=j+1 := by omega
  have h3 : p+1-i=j := by omega
  have hleft : pairLeftCoefficient (p+1) (i+1) =
      ((i+1:ℝ)-j) * paperPairWeight (p+1) (i+1) j := by
    unfold pairLeftCoefficient
    rw [h1]
    split_ifs with h
    · push_cast; rfl
    · have he : i+1=j := by omega
      simp [← he]
  rw [hleft]
  simp only [pairLeftCoefficient, h2, h3, hlt,
    show i<j+1 by omega, if_true, Nat.cast_add, Nat.cast_one]
  have h := paperPair_signed_lower p i j
  linear_combination h

/-- The diagonal and reversed-target cases retain their genuine exterior zero. -/
private theorem pair_lower_coefficient_wedge (p i j : ℕ) (hij : i+j=p+1) :
    ((pairLeftCoefficient (p+1) (i+1):ℂ) * (Real.sqrt (i+1:ℝ):ℂ) +
      (pairLeftCoefficient (p+1) i:ℂ) * (Real.sqrt (j+1:ℝ):ℂ)) •
      (formalJet i*formalJet j) =
    (Real.sqrt (2*(p+1:ℝ)):ℂ) • ((pairLeftCoefficient p i:ℂ) •
      (formalJet i*formalJet j)) := by
  rcases lt_trichotomy i j with h | h | h
  · rw [smul_smul]
    congr 1
    exact_mod_cast pair_lower_coefficient_lt p i j hij h
  · subst j
    simp only [formalJet, ExteriorAlgebra.ι_sq_zero, smul_zero]
  · have h1 : p+1+1-(i+1)=j := by omega
    have h2 : p+1+1-i=j+1 := by omega
    have h3 : p+1-i=j := by omega
    simp [pairLeftCoefficient, h1, h2, h3, show ¬ i+1<j by omega,
      show ¬ i<j+1 by omega, show ¬ i<j by omega]

def loweredPair (p : ℕ) : FormalExterior :=
  ∑ i ∈ Finset.range (p+2), (pairLeftCoefficient p i:ℂ) •
    ((Real.sqrt (i:ℝ):ℂ) • (formalJet (i-1)*formalJet (p+1-i)) +
     (Real.sqrt ((p+1-i:ℕ):ℝ):ℂ) • (formalJet i*formalJet (p+1-i-1)))

theorem loweredPair_zero : loweredPair 0 = 0 := by
  norm_num [loweredPair, pairLeftCoefficient, paperPairWeight, formalJet,
    ExteriorAlgebra.ι_sq_zero, Finset.sum_range_succ]

/-- Actual original normalized pair ladder; every orbital index remains Nat. -/
theorem loweredPair_succ (p : ℕ) :
    loweredPair (p+1) = (Real.sqrt (2*(p+1:ℝ)):ℂ) • formalPair p := by
  classical
  unfold loweredPair
  simp only [smul_add, Finset.sum_add_distrib, smul_smul]
  have hleft :
      (∑ i ∈ Finset.range (p+1+2),
        ((pairLeftCoefficient (p+1) i:ℂ)*(Real.sqrt (i:ℝ):ℂ)) •
          (formalJet (i-1)*formalJet (p+1+1-i))) =
      ∑ i ∈ Finset.range (p+2),
        ((pairLeftCoefficient (p+1) (i+1):ℂ)*(Real.sqrt (i+1:ℝ):ℂ)) •
          (formalJet i*formalJet (p+1-i)) := by
    rw [show p+1+2=(p+2)+1 by omega, Finset.sum_range_succ']
    simp only [Nat.cast_zero, Real.sqrt_zero, Complex.ofReal_zero,
      mul_zero, zero_smul, add_zero, Nat.add_sub_cancel, Nat.add_sub_add_right,
      Nat.cast_add, Nat.cast_one]
  have hright :
      (∑ i ∈ Finset.range (p+1+2),
        ((pairLeftCoefficient (p+1) i:ℂ)*(Real.sqrt ((p+1+1-i:ℕ):ℝ):ℂ)) •
          (formalJet i*formalJet (p+1+1-i-1))) =
      ∑ i ∈ Finset.range (p+2),
        ((pairLeftCoefficient (p+1) i:ℂ)*(Real.sqrt (((p+1-i)+1:ℕ):ℝ):ℂ)) •
          (formalJet i*formalJet (p+1-i)) := by
    rw [show p+1+2=(p+2)+1 by omega, Finset.sum_range_succ]
    have hend : p+1+1-(p+2)=0 := by omega
    simp only [hend, Nat.cast_zero, Real.sqrt_zero, Complex.ofReal_zero,
      mul_zero, zero_smul, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have ha : p+1+1-i=(p+1-i)+1 := by omega
    have hb : p+1+1-i-1=p+1-i := by omega
    rw [hb, ha]
  rw [hleft, hright, ← Finset.sum_add_distrib]
  simp_rw [← add_smul]
  rw [formalPair, Fin.sum_univ_eq_sum_range
    (fun i : ℕ => (pairLeftCoefficient p i : ℂ) •
      (formalJet i * formalJet (p+1-i))) (p+2), Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [Nat.cast_add, Nat.cast_one] using
    pair_lower_coefficient_wedge p i (p+1-i)
      (by have := Finset.mem_range.mp hi; omega)

/-- The spectator is untouched by the pair sum, and its own label has the
original sqrt(j) lowering factor. -/
theorem realize_lower_three_pair_split (p j : ℕ) :
    realize 3 (wordLower 3 (threeCoefficients p j)) =
      loweredPair p * formalJet j +
      (Real.sqrt (j:ℝ):ℂ) • formalThreeSeed p (j-1) := by
  rw [realize_lower_threeCoefficients]
  unfold loweredPair formalThreeSeed formalPair
  rw [← Fin.sum_univ_eq_sum_range
    (fun i : ℕ => (pairLeftCoefficient p i : ℂ) •
      ((Real.sqrt (i:ℝ):ℂ) • (formalJet (i-1)*formalJet (p+1-i)) +
       (Real.sqrt ((p+1-i:ℕ):ℝ):ℂ) • (formalJet i*formalJet (p+1-i-1)))) (p+2)]
  simp only [Finset.sum_mul, smul_mul_assoc, add_mul, smul_add,
    Finset.sum_add_distrib, Finset.smul_sum, mul_assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [smul_comm]

/-- Pair-plus-spectator lowering, directly on the original exterior source. -/
theorem realize_lower_three_succ (p j : ℕ) :
    realize 3 (wordLower 3 (threeCoefficients (p+1) j)) =
      (Real.sqrt (2*(p+1:ℝ)):ℂ) • formalThreeSeed p j +
      (Real.sqrt (j:ℝ):ℂ) • formalThreeSeed (p+1) (j-1) := by
  rw [realize_lower_three_pair_split, loweredPair_succ, smul_mul_assoc]
  rfl

#print axioms loweredPair_zero
#print axioms loweredPair_succ
#print axioms realize_lower_three_succ
#print axioms realize_lower_three_pair_split

end TorusLean.Shared.ThermalCoherentFermionCOMWords
