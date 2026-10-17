import torus.shared.FermionLocalJetFourCouplingGeneralSourcePolynomial

/-! Rebuilt successfully with Lean 4.34.1 in the selected 3,177-module closure.
See [validation scope](../../../REBUILD.md) and ../../../REBUILD_VALIDATION.json.
No inverse factorials, quotient equality, finite evaluator, or target assumptions.
This is the denominator-free version of the exponential-generating-function bridge. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators
open GeneralSourcePolynomialCandidate
namespace GeneralSourceEncodingCandidate

def integerFactorialWeight (v : Fin 4 → ℕ) : ℤ :=
  ∏ i : Fin 4, ((v i).factorial : ℤ)

/-- E(x^m)=m!·single m. This is the inverse of exponential polynomial
coordinates on its image, but needs neither denominators nor a surjectivity claim. -/
def factorialWeightedWords : FourPolynomial →ₗ[ℤ] IntegerFourWords :=
  (Finsupp.linearCombination ℤ (fun m : Fin 4 →₀ ℕ =>
    Finsupp.single (fun i => m i) (integerFactorialWeight (fun i => m i)))) ∘ₗ
      (AddMonoidAlgebra.coeffLinearEquiv ℤ).toLinearMap

@[simp] theorem factorialWeightedWords_monomial (m : Fin 4 →₀ ℕ) (z : ℤ) :
    factorialWeightedWords (MvPolynomial.monomial m z) =
      Finsupp.single (fun i => m i) (z * integerFactorialWeight (fun i => m i)) := by
  change (Finsupp.linearCombination ℤ (fun n : Fin 4 →₀ ℕ =>
    Finsupp.single (fun i => n i) (integerFactorialWeight (fun i => n i))))
      (Finsupp.single m z) = _
  rw [Finsupp.linearCombination_single]
  simp only [Finsupp.smul_single,smul_eq_mul]

theorem integerFactorialWeight_update (v : Fin 4 → ℕ) (i : Fin 4) (n : ℕ) :
    integerFactorialWeight (Function.update v i n) =
      (n.factorial : ℤ) * ∏ j ∈ Finset.univ.erase i, ((v j).factorial : ℤ) := by
  unfold integerFactorialWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

theorem integerFactorialWeight_raise (v : Fin 4 → ℕ) (i : Fin 4) :
    integerFactorialWeight (Function.update v i (v i+1)) =
      ((v i+1 : ℕ) : ℤ) * integerFactorialWeight v := by
  rw [integerFactorialWeight_update]
  unfold integerFactorialWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  simp only [Nat.factorial_succ,Nat.cast_mul]
  ring

theorem integerFactorialWeight_lower (v : Fin 4 → ℕ) (i : Fin 4) (hi : v i≠0) :
    integerFactorialWeight v =
      (v i : ℤ) * integerFactorialWeight (Function.update v i (v i-1)) := by
  have hn : v i-1+1=v i := by omega
  have hf : ((v i).factorial : ℤ) =
      (v i : ℤ) * ((v i-1).factorial : ℤ) := by
    have h := Nat.factorial_succ (v i-1)
    rw [hn] at h
    exact_mod_cast h
  rw [integerFactorialWeight_update]
  unfold integerFactorialWeight
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  rw [hf]
  ring

theorem exponent_single_add_vec (m : Fin 4 →₀ ℕ) (i : Fin 4) :
    (fun j : Fin 4 => ((Finsupp.single i 1 + m : Fin 4 →₀ ℕ) j)) =
      Function.update (fun j => m j) i (m i+1) := by
  funext j
  by_cases h : j=i
  · subst j
    simp [Nat.add_comm]
  · simp [h,Ne.symm h]

theorem exponent_sub_single_vec (m : Fin 4 →₀ ℕ) (i : Fin 4) :
    (fun j : Fin 4 => ((m-Finsupp.single i 1 : Fin 4 →₀ ℕ) j)) =
      Function.update (fun j => m j) i (m i-1) := by
  funext j
  by_cases h : j=i
  · subst j
    simp
  · simp [h,Ne.symm h]

/-- A single polynomial multiplication gives exactly the original (label+1)
raising coefficient; no global normalizing factor appears. -/
theorem factorialWeightedWords_mul_X_monomial (m : Fin 4 →₀ ℕ) (z : ℤ) (i : Fin 4) :
    factorialWeightedWords (MvPolynomial.X i * MvPolynomial.monomial m z) =
      Finsupp.single (Function.update (fun j => m j) i (m i+1))
        ((z * integerFactorialWeight (fun j => m j)) * ((m i+1 : ℕ) : ℤ)) := by
  rw [MvPolynomial.X,MvPolynomial.monomial_mul_monomial,one_mul,
    factorialWeightedWords_monomial,exponent_single_add_vec,integerFactorialWeight_raise]
  congr 1
  ring

/-- The derivative gives exactly coefficient-one lowering, with the original
zero-label guard retained. -/
theorem factorialWeightedWords_pderiv_monomial (m : Fin 4 →₀ ℕ) (z : ℤ) (i : Fin 4) :
    factorialWeightedWords (MvPolynomial.pderiv i (MvPolynomial.monomial m z)) =
      if m i=0 then 0 else
        Finsupp.single (Function.update (fun j => m j) i (m i-1))
          (z * integerFactorialWeight (fun j => m j)) := by
  rw [MvPolynomial.pderiv_monomial,factorialWeightedWords_monomial,
    exponent_sub_single_vec]
  by_cases hi : m i=0
  · simp [hi]
  · rw [if_neg hi,integerFactorialWeight_lower (fun j => m j) i hi]
    congr 1
    ring

theorem collectiveSum_eq_sum : collectiveSum = ∑ i : Fin 4, (MvPolynomial.X i : FourPolynomial) := by
  rw [Fin.sum_univ_four]
  rfl

theorem collectiveDerivative_eq_sum (p : FourPolynomial) :
    collectiveDerivative p = ∑ i : Fin 4, MvPolynomial.pderiv i p := by
  rw [Fin.sum_univ_four]
  rfl

/-- Intertwining with the actual `raiseIntegerFourWords` from IntegerWords. -/
theorem factorialWeightedWords_raise (p : FourPolynomial) :
    factorialWeightedWords (collectiveSum*p) = raiseIntegerFourWords (factorialWeightedWords p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [mul_add,map_add,hp,hq]
  | monomial m z =>
    rw [collectiveSum_eq_sum,Finset.sum_mul,map_sum,factorialWeightedWords_monomial]
    simp only [raiseIntegerFourWords,Finsupp.linearCombination_single,Finset.smul_sum,
      Finsupp.smul_single,smul_eq_mul,factorialWeightedWords_mul_X_monomial]

/-- Intertwining with the actual `lowerIntegerFourWords` from IntegerWords. -/
theorem factorialWeightedWords_lower (p : FourPolynomial) :
    factorialWeightedWords (collectiveDerivative p) = lowerIntegerFourWords (factorialWeightedWords p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add,hp,hq]
  | monomial m z =>
    rw [collectiveDerivative_eq_sum,map_sum,factorialWeightedWords_monomial]
    simp only [lowerIntegerFourWords,Finsupp.linearCombination_single,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [factorialWeightedWords_pderiv_monomial]
    by_cases hz : m i=0
    · simp [hz]
    · simp [hz,Finsupp.smul_single,smul_eq_mul]

end GeneralSourceEncodingCandidate
end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceEncodingCandidate.factorialWeightedWords_monomial
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceEncodingCandidate.integerFactorialWeight_update
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceEncodingCandidate.integerFactorialWeight_raise
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceEncodingCandidate.integerFactorialWeight_lower
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceEncodingCandidate.exponent_single_add_vec
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceEncodingCandidate.exponent_sub_single_vec
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceEncodingCandidate.factorialWeightedWords_mul_X_monomial
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceEncodingCandidate.factorialWeightedWords_pderiv_monomial
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceEncodingCandidate.collectiveSum_eq_sum
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceEncodingCandidate.collectiveDerivative_eq_sum
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceEncodingCandidate.factorialWeightedWords_raise
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceEncodingCandidate.factorialWeightedWords_lower
