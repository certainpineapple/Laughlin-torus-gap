import torus.shared.ThermalCoherentFermionCOMWordsOps

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionCOMWords
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.ThermalCoherentFermionJetWord
open TorusLean.Shared.ParameterCellAdjoint TorusLean.Shared.ParameterRawJetLadder
open scoped ContDiff BigOperators ComplexConjugate

theorem realize_raise (k : ℕ) (c : WordCoefficients k) :
    realize k (wordRaise k c) = raiseFiniteExteriorWord k c.support c id := by
  rw [wordRaise, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, map_sum, map_smul]
  simp only [realize, Finsupp.linearCombination_single, one_smul,
    raiseFiniteExteriorWord, raiseExteriorWord, id_eq]

#print axioms realize_raise

end TorusLean.Shared.ThermalCoherentFermionCOMWords
