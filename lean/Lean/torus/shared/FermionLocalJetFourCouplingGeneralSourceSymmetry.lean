import torus.shared.FermionLocalJetFourCouplingGeneralSourceEncoding
import torus.shared.FermionLocalJetFourCouplingGeneralHalfSpace

/-! Rebuilt successfully with Lean 4.34.1 in the selected 3,177-module closure.
See [validation scope](../../../REBUILD.md) and ../../../REBUILD_VALIDATION.json. Rename uses the inverse permutation
in the original word convention. Only the two self-inverse swaps are needed
by the source proof, but the correctly oriented general bridge is short. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open scoped BigOperators
open GeneralSourcePolynomialCandidate GeneralSourceEncodingCandidate GeneralHalfSpaceCandidate
open DegreeOneLadderBridgeCandidate
namespace GeneralSourceSymmetryCandidate

theorem integerFactorialWeight_comp (v : Fin 4 → ℕ) (σ : Equiv.Perm (Fin 4)) :
    integerFactorialWeight (v ∘ σ)=integerFactorialWeight v := by
  exact Equiv.prod_comp σ (fun i => ((v i).factorial : ℤ))

theorem exponent_mapDomain_perm_vec (m : Fin 4 →₀ ℕ) (σ : Equiv.Perm (Fin 4)) :
    (fun i => (m.mapDomain σ) i) = (fun i => m i) ∘ σ.symm := by
  funext i
  exact Finsupp.mapDomain_equiv_apply m i

/-- Correct inverse convention: rename σ sends X_i to X_(σ i), so the
new word label is oldLabel∘σ⁻¹. -/
theorem factorialWeightedWords_rename (σ : Equiv.Perm (Fin 4)) (p : FourPolynomial) :
    factorialWeightedWords (MvPolynomial.rename σ p) =
      permuteIntegerFourWords σ.symm (factorialWeightedWords p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp only [map_add,hp,hq]
  | monomial m z =>
    rw [MvPolynomial.rename_monomial,factorialWeightedWords_monomial,
      factorialWeightedWords_monomial,permute_single,
      exponent_mapDomain_perm_vec,integerFactorialWeight_comp]

theorem fullSourceWords_skew01 (D T r : ℕ) :
    permuteIntegerFourWords (Equiv.swap (0 : Fin 4) 1)
      (factorialWeightedWords (fullSourcePolynomial D T r)) =
        -factorialWeightedWords (fullSourcePolynomial D T r) := by
  have h := congrArg factorialWeightedWords (fullSourcePolynomial_swap01 D T r)
  rw [factorialWeightedWords_rename,map_neg] at h
  simpa only [Equiv.symm_swap] using h

theorem fullSourceWords_skew23 (D T r : ℕ) (hr : Odd r) :
    permuteIntegerFourWords (Equiv.swap (2 : Fin 4) 3)
      (factorialWeightedWords (fullSourcePolynomial D T r)) =
        -factorialWeightedWords (fullSourcePolynomial D T r) := by
  have h := congrArg factorialWeightedWords (fullSourcePolynomial_swap23 D T r hr)
  rw [factorialWeightedWords_rename,map_neg] at h
  simpa only [Equiv.symm_swap] using h

/-- No source-identification premise is hidden here. The only remaining
source-specific obligation is originalSource=orderedPairMask(E P). -/
theorem fullSourceWords_alternate_four_mask (D T r : ℕ) (hr : Odd r) :
    alternateIntegerFourWords (factorialWeightedWords (fullSourcePolynomial D T r)) =
      (4 : ℤ) • alternateIntegerFourWords
        (orderedPairMask (factorialWeightedWords (fullSourcePolynomial D T r))) := by
  exact alternate_orderedPairMask _ (fullSourceWords_skew01 D T r)
    (fullSourceWords_skew23 D T r hr)

end GeneralSourceSymmetryCandidate
end TorusLean.Shared.FermionLocalJet.FourCoupling

#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceSymmetryCandidate.integerFactorialWeight_comp
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceSymmetryCandidate.exponent_mapDomain_perm_vec
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceSymmetryCandidate.factorialWeightedWords_rename
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceSymmetryCandidate.fullSourceWords_skew01
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceSymmetryCandidate.fullSourceWords_skew23
#print axioms TorusLean.Shared.FermionLocalJet.FourCoupling.GeneralSourceSymmetryCandidate.fullSourceWords_alternate_four_mask
