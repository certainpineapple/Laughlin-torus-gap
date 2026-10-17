import torus.shared.FermionLocalJetFourCouplingDescendantWedge
import torus.shared.ThermalCoherentFermionCOMWordsRealize

/-! Exact finite ordered-word presentations of the original four-body columns.
This is a source identity in the actual exterior algebra. No vacuum or COM
recurrence is asserted here; those remain separate algebraic obligations. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.ThermalCoherentFermionJetWord
open TorusLean.Shared.ThermalCoherentFermionCOMWords
open scoped BigOperators

 theorem formalExteriorWord_four (a b j k : ℕ) :
    formalExteriorWord 4 ![a,b,j,k] =
      formalJet a * formalJet b * formalJet j * formalJet k := by
  simp [formalExteriorWord, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, formalJet, mul_assoc, Matrix.vecTail]

/-- Original v_p coefficients, with the two spectator labels kept ordered. -/
def fourInputWords (p j k : ℕ) : WordCoefficients 4 :=
  ∑ a : Fin (p+2), (pairLeftCoefficient p a.val : ℂ) •
    Finsupp.single ![a.val,p+1-a.val,j,k] 1

 theorem realize_fourInputWords (p j k : ℕ) :
    realize 4 (fourInputWords p j k) =
      formalPair p * formalJet j * formalJet k := by
  simp only [fourInputWords, map_sum, map_smul, realize,
    Finsupp.linearCombination_single, one_smul, formalExteriorWord_four,
    formalPair, Finset.sum_mul, smul_mul_assoc]

/-- All original full-T S45 entries are retained, including their signs. -/
def descendantWords (D T r : ℕ) : WordCoefficients 4 :=
  ∑ q : HalfInputIndex T,
    paperS45 r D T q.val.1.val q.val.2.val (T-q.val.1.val-q.val.2.val) •
      fourInputWords q.val.1.val q.val.2.val (T-q.val.1.val-q.val.2.val)

 theorem realize_descendantWords (D T r : ℕ) :
    realize 4 (descendantWords D T r) = formalDescendantColumn D T r := by
  simp only [descendantWords, map_sum, map_smul, realize_fourInputWords,
    formalDescendantColumn]

 def highestCoupledWords (D : ℕ) (r : OddMode D) : WordCoefficients 4 :=
  descendantWords D D r.val.val

 theorem realize_highestCoupledWords (D : ℕ) (r : OddMode D) :
    realize 4 (highestCoupledWords D r) = formalCoupledColumn D r := by
  rw [highestCoupledWords, realize_descendantWords, formalDescendantColumn_highest]

#print axioms formalExteriorWord_four
#print axioms realize_fourInputWords
#print axioms realize_descendantWords
#print axioms realize_highestCoupledWords
end TorusLean.Shared.FermionLocalJet.FourCoupling
