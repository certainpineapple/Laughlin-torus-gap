import torus.shared.FermionPairRaiseCoefficients
import torus.shared.FermionPairLowerExterior

/-! The true upward pair/spectator action, preserving the original m=1 pair
orientation.  This is a direct finite coefficient proof. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionCOMWords
open TorusLean.Shared.FermionRelativeFrame
open TorusLean.Shared.FermionLocalJet TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.ThermalCoherentFermionAnchored
open TorusLean.Shared.ThermalCoherentFermionJetWord
open scoped BigOperators

private theorem pair_raise_coefficient_wedge (p i j : ℕ) (hij : i+j=p+2) :
    ((pairLeftCoefficient p (i-1):ℂ)*(Real.sqrt (i:ℝ):ℂ) +
      (pairLeftCoefficient p i:ℂ)*(Real.sqrt (j:ℝ):ℂ)) • (formalJet i*formalJet j) =
      (Real.sqrt (2*(p+1:ℝ)):ℂ) •
        ((pairLeftCoefficient (p+1) i:ℂ) • (formalJet i*formalJet j)) := by
  rcases lt_trichotomy i j with h | h | h
  · rw [smul_smul]
    congr 1
    exact_mod_cast pair_raise_coefficient_lt p i j hij h
  · subst j
    simp only [formalJet, ExteriorAlgebra.ι_sq_zero, smul_zero]
  · have hn : ¬ i-1 < p+1-(i-1) := by omega
    have hn' : ¬ i < p+1-i := by omega
    have hn'' : ¬ i < p+1+1-i := by omega
    simp [pairLeftCoefficient, hn, hn', hn'']

def raisedPair (p : ℕ) : FormalExterior :=
  ∑ i ∈ Finset.range (p+2), (pairLeftCoefficient p i:ℂ) •
    ((Real.sqrt (i+1:ℝ):ℂ) • (formalJet (i+1)*formalJet (p+1-i)) +
     (Real.sqrt (((p+1-i)+1:ℕ):ℝ):ℂ) • (formalJet i*formalJet ((p+1-i)+1)))

theorem raisedPair_eq (p : ℕ) :
    raisedPair p = (Real.sqrt (2*(p+1:ℝ)):ℂ) • formalPair (p+1) := by
  classical
  unfold raisedPair
  simp only [smul_add, Finset.sum_add_distrib, smul_smul]
  have hleft :
      (∑ i ∈ Finset.range (p+2),
        ((pairLeftCoefficient p i:ℂ)*(Real.sqrt (i+1:ℝ):ℂ)) •
          (formalJet (i+1)*formalJet (p+1-i))) =
      ∑ i ∈ Finset.range (p+3),
        ((pairLeftCoefficient p (i-1):ℂ)*(Real.sqrt (i:ℝ):ℂ)) •
          (formalJet i*formalJet (p+2-i)) := by
    symm
    rw [show p+3=(p+2)+1 by omega, Finset.sum_range_succ']
    simp only [Nat.cast_zero, Real.sqrt_zero, Complex.ofReal_zero,
      mul_zero, zero_smul, add_zero, Nat.add_sub_cancel, Nat.add_sub_add_right,
      Nat.cast_add, Nat.cast_one]
    apply Finset.sum_congr rfl
    intro i hi
    rw [show p+2-(i+1)=p+1-i by omega]
  have hright :
      (∑ i ∈ Finset.range (p+2),
        ((pairLeftCoefficient p i:ℂ)*(Real.sqrt (((p+1-i)+1:ℕ):ℝ):ℂ)) •
          (formalJet i*formalJet ((p+1-i)+1))) =
      ∑ i ∈ Finset.range (p+3),
        ((pairLeftCoefficient p i:ℂ)*(Real.sqrt ((p+2-i:ℕ):ℝ):ℂ)) •
          (formalJet i*formalJet (p+2-i)) := by
    symm
    rw [show p+3=(p+2)+1 by omega, Finset.sum_range_succ]
    simp only [Nat.sub_self, Nat.cast_zero, Real.sqrt_zero, Complex.ofReal_zero,
      mul_zero, zero_smul, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    have he : (p+1-i)+1=p+2-i := by have := Finset.mem_range.mp hi; omega
    rw [he]
  rw [hleft, hright, ← Finset.sum_add_distrib]
  simp_rw [← add_smul]
  rw [formalPair, Fin.sum_univ_eq_sum_range
    (fun i : ℕ => (pairLeftCoefficient (p+1) i : ℂ) •
      (formalJet i * formalJet (p+1+1-i))) (p+1+2), Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  exact pair_raise_coefficient_wedge p i (p+2-i)
    (by have := Finset.mem_range.mp hi; omega)

theorem realize_raise_three_word (a b c : ℕ) :
    realize 3 (wordRaise 3 (Finsupp.single ![a,b,c] 1)) =
      (Real.sqrt (a+1:ℝ):ℂ) • (formalJet (a+1)*formalJet b*formalJet c) +
      (Real.sqrt (b+1:ℝ):ℂ) • (formalJet a*formalJet (b+1)*formalJet c) +
      (Real.sqrt (c+1:ℝ):ℂ) • (formalJet a*formalJet b*formalJet (c+1)) := by
  classical
  have h0 : Function.update ![a,b,c] (0:Fin 3) (a+1) = ![a+1,b,c] := by
    ext i; fin_cases i <;> simp
  have h1 : Function.update ![a,b,c] (1:Fin 3) (b+1) = ![a,b+1,c] := by
    ext i; fin_cases i <;> simp
  have h2 : Function.update ![a,b,c] (2:Fin 3) (c+1) = ![a,b,c+1] := by
    ext i; fin_cases i <;> simp
  simp only [wordRaise, Finsupp.linearCombination_single, one_smul,
    map_sum, map_smul, realize, Finsupp.linearCombination_single, one_smul]
  rw [Fin.sum_univ_three]
  have htail : (![b,c] ∘ Fin.succ) (0 : Fin 1) = c := rfl
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, htail, h0, h1, h2, formalExteriorWord_three]

/-- The original pair/spectator upward ladder, with both distinct charges. -/
theorem realize_raise_threeCoefficients (p j : ℕ) :
    realize 3 (wordRaise 3 (threeCoefficients p j)) =
      (Real.sqrt (2*(p+1:ℝ)):ℂ) • formalThreeSeed (p+1) j +
      (Real.sqrt (j+1:ℝ):ℂ) • formalThreeSeed p (j+1) := by
  have he : realize 3 (wordRaise 3 (threeCoefficients p j)) =
      raisedPair p * formalJet j + (Real.sqrt (j+1:ℝ):ℂ) • formalThreeSeed p (j+1) := by
    simp only [threeCoefficients, map_sum, map_smul, realize_raise_three_word]
    unfold raisedPair formalThreeSeed formalPair
    rw [← Fin.sum_univ_eq_sum_range
      (fun i : ℕ => (pairLeftCoefficient p i : ℂ) •
        ((Real.sqrt (i+1:ℝ):ℂ) • (formalJet (i+1)*formalJet (p+1-i)) +
         (Real.sqrt (((p+1-i)+1:ℕ):ℝ):ℂ) •
           (formalJet i*formalJet ((p+1-i)+1)))) (p+2)]
    simp only [Finset.sum_mul, smul_mul_assoc, add_mul, smul_add,
      Finset.sum_add_distrib, Finset.smul_sum, mul_assoc, Nat.cast_add, Nat.cast_one]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [smul_comm]
  rw [he, raisedPair_eq, smul_mul_assoc]
  rfl

#print axioms raisedPair_eq
#print axioms realize_raise_threeCoefficients
#print axioms realize_raise_three_word

end TorusLean.Shared.ThermalCoherentFermionCOMWords
