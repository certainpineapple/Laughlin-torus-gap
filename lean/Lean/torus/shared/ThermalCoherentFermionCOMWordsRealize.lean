import torus.shared.ThermalCoherentFermionJetWordFiniteActions

set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionCOMWords
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.ThermalCoherentFermionJetWord
open TorusLean.Shared.ParameterCellAdjoint TorusLean.Shared.ParameterRawJetLadder
open scoped ContDiff BigOperators ComplexConjugate

/-- Finite coefficients on ordered Nat-labelled words.  Antisymmetry is
implemented by `realize`, rather than by identifying this with a boson core. -/
abbrev WordCoefficients (k : ℕ) := (Fin k → ℕ) →₀ ℂ

def realize (k : ℕ) : WordCoefficients k →ₗ[ℂ] FormalExterior :=
  Finsupp.linearCombination ℂ (formalExteriorWord k)

theorem realize_eq_finite (k : ℕ) (c : WordCoefficients k) :
    realize k c = finiteExteriorWord k c.support c id := rfl

#print axioms realize_eq_finite


end TorusLean.Shared.ThermalCoherentFermionCOMWords
