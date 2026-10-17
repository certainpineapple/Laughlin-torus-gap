import torus.shared.ThermalCoherentFermionCOMWordsRealize

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionCOMWords
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.ThermalCoherentFermionJetWord
open TorusLean.Shared.ParameterCellAdjoint TorusLean.Shared.ParameterRawJetLadder
open scoped ContDiff BigOperators ComplexConjugate

def wordRaise (k : ℕ) : WordCoefficients k →ₗ[ℂ] WordCoefficients k :=
  Finsupp.linearCombination ℂ (fun j : Fin k → ℕ => ∑ a : Fin k,
    (Real.sqrt (j a+1:ℝ):ℂ) • Finsupp.single (Function.update j a (j a+1)) 1)

def wordLower (k : ℕ) : WordCoefficients k →ₗ[ℂ] WordCoefficients k :=
  Finsupp.linearCombination ℂ (fun j : Fin k → ℕ => ∑ a : Fin k,
    (Real.sqrt (j a:ℝ):ℂ) • Finsupp.single (Function.update j a (j a-1)) 1)


end TorusLean.Shared.ThermalCoherentFermionCOMWords
