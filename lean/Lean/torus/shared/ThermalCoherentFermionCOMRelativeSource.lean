import torus.shared.ThermalCoherentFermionCOMCell
import torus.shared.ThermalCoherentFermionAnchoredSource

/-! The COM presentation uses the original pair and relative coefficients.
All three orbital labels are Nat, and every exterior product keeps its order. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionCOMWords
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.FermionRelativeFrame
open TorusLean.Shared.FermionLocalJet TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.ThermalCoherentFermionJetWord
open TorusLean.Shared.ThermalCoherentFermionAnchored
open scoped BigOperators

theorem formalExteriorWord_three (a b c : ℕ) :
    formalExteriorWord 3 ![a,b,c] = formalJet a * formalJet b * formalJet c := by
  simp [formalExteriorWord, formalJet, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, Matrix.vecHead, Matrix.vecTail, mul_assoc]

def threeCoefficients (p j : ℕ) : WordCoefficients 3 :=
  ∑ i : Fin (p+2), (pairLeftCoefficient p i.val : ℂ) •
    Finsupp.single ![i.val,p+1-i.val,j] 1

def relativeCoefficients (d : ℕ) : WordCoefficients 3 :=
  ∑ p ∈ Finset.range (d+1), (paperPauliCoefficient d p : ℂ) • threeCoefficients p (d-p)

/-- The original pair normalization and original negative ground orientation. -/
theorem realize_threeCoefficients (p j : ℕ) :
    realize 3 (threeCoefficients p j) = formalThreeSeed p j := by
  simp only [threeCoefficients, map_sum, map_smul, realize,
    Finsupp.linearCombination_single, one_smul, formalExteriorWord_three,
    formalThreeSeed, formalPair, Finset.sum_mul, smul_mul_assoc]

/-- No renormalization or alternate Jacobi source is introduced. -/
theorem realize_relativeCoefficients (d : ℕ) :
    realize 3 (relativeCoefficients d) = formalRelativeSeed d := by
  simp only [relativeCoefficients, map_sum, map_smul, realize_threeCoefficients,
    formalRelativeSeed]

/-- Literal total lowering on a three-jet wedge, including zero-label terms. -/
theorem realize_lower_three_word (a b c : ℕ) :
    realize 3 (wordLower 3 (Finsupp.single ![a,b,c] 1)) =
      (Real.sqrt (a:ℝ):ℂ) • (formalJet (a-1)*formalJet b*formalJet c) +
      (Real.sqrt (b:ℝ):ℂ) • (formalJet a*formalJet (b-1)*formalJet c) +
      (Real.sqrt (c:ℝ):ℂ) • (formalJet a*formalJet b*formalJet (c-1)) := by
  classical
  have h0 : Function.update ![a,b,c] (0:Fin 3) (a-1) = ![a-1,b,c] := by
    ext i; fin_cases i <;> simp
  have h1 : Function.update ![a,b,c] (1:Fin 3) (b-1) = ![a,b-1,c] := by
    ext i; fin_cases i <;> simp
  have h2 : Function.update ![a,b,c] (2:Fin 3) (c-1) = ![a,b,c-1] := by
    ext i; fin_cases i <;> simp
  simp only [wordLower, Finsupp.linearCombination_single, one_smul,
    map_sum, map_smul, realize, Finsupp.linearCombination_single, one_smul]
  rw [Fin.sum_univ_three]
  have htail : (![b,c] ∘ Fin.succ) (0 : Fin 1) = c := rfl
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.vecHead, Matrix.vecTail, htail, h0, h1, h2, formalExteriorWord_three]

/-- Finite original pair coefficients remain visible for the Jacobi/relative
vacuum cancellation.  This is the actual exterior lowering, not an assumed
polynomial differential action. -/
theorem realize_lower_threeCoefficients (p j : ℕ) :
    realize 3 (wordLower 3 (threeCoefficients p j)) =
      ∑ i : Fin (p+2), (pairLeftCoefficient p i.val : ℂ) •
        ((Real.sqrt (i.val:ℝ):ℂ) •
            (formalJet (i.val-1)*formalJet (p+1-i.val)*formalJet j) +
         (Real.sqrt ((p+1-i.val:ℕ):ℝ):ℂ) •
            (formalJet i.val*formalJet (p+1-i.val-1)*formalJet j) +
         (Real.sqrt (j:ℝ):ℂ) •
            (formalJet i.val*formalJet (p+1-i.val)*formalJet (j-1))) := by
  simp only [threeCoefficients, map_sum, map_smul, realize_lower_three_word]

theorem realize_lower_relativeCoefficients (d : ℕ) :
    realize 3 (wordLower 3 (relativeCoefficients d)) =
      ∑ p ∈ Finset.range (d+1), (paperPauliCoefficient d p : ℂ) •
        realize 3 (wordLower 3 (threeCoefficients p (d-p))) := by
  simp only [relativeCoefficients, map_sum, map_smul]

/-- The dual function at level zero is literally the original exterior source. -/
theorem relative_wordDual_eq (G : Geometry) (theta : Twist)
    (q : Space (physicalQ G theta)) (d : ℕ) :
    wordDual G theta 3 q (relativeCoefficients d) =
      exteriorSeedDual G theta q (formalRelativeSeed d) := by
  change exteriorSeedDual G theta q (realize 3 (relativeCoefficients d)) = _
  rw [realize_relativeCoefficients]

#print axioms realize_relativeCoefficients
#print axioms realize_lower_threeCoefficients
#print axioms formalExteriorWord_three
#print axioms realize_threeCoefficients
#print axioms realize_lower_three_word
#print axioms realize_lower_relativeCoefficients
#print axioms relative_wordDual_eq

end TorusLean.Shared.ThermalCoherentFermionCOMWords
