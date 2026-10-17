import torus.shared.ThermalCoherentFermionCOMWordsRaise

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionCOMWords
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.ThermalCoherentFermionJetWord
open TorusLean.Shared.ParameterCellAdjoint TorusLean.Shared.ParameterRawJetLadder
open scoped ContDiff BigOperators ComplexConjugate

theorem realize_lower (k : ℕ) (c : WordCoefficients k) :
    realize k (wordLower k c) = lowerFiniteExteriorWord k c.support c id := by
  rw [wordLower, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, map_sum, map_smul]
  simp only [realize, Finsupp.linearCombination_single, one_smul,
    lowerFiniteExteriorWord, lowerExteriorWord, id_eq]



#print axioms realize_lower

end TorusLean.Shared.ThermalCoherentFermionCOMWords
