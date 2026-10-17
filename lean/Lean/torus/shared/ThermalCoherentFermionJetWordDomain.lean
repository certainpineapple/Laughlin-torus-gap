import torus.shared.ThermalCoherentFermionJetWordActions

/-! Fixed finite alternating source families have the actual smooth magnetic
parameter domain and the true total-mode parameter actions. The displayed
word representation is retained; no unsupported infinite exterior domain or
polynomial commutative substitution is introduced. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionJetWord
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.ParameterCellAdjoint TorusLean.Shared.ParameterRawJetLadder
open TorusLean.Shared.BosonAnchoredSeedActions
open scoped BigOperators ContDiff

def finiteExteriorWord {I : Type*} (k : ℕ) (s : Finset I)
    (c : I → ℂ) (j : I → Fin k → ℕ) : FormalExterior :=
  ∑ i ∈ s, c i • formalExteriorWord k (j i)

def exteriorSeedDual (G : Geometry) (theta : Twist)
    (q : Space (physicalQ G theta)) (v : FormalExterior) (R : ℂ) : ℂ :=
  occupationInner (physicalQ G theta) q (rawJetExteriorMap G theta R v)

/-- Both the source and its real parameter image use the same finite sum. -/
theorem exteriorSeedDual_finiteWord {I : Type*} (G : Geometry) (theta : Twist)
    (k : ℕ) (s : Finset I) (c : I → ℂ) (j : I → Fin k → ℕ)
    (q : Space (physicalQ G theta)) :
    exteriorSeedDual G theta q (finiteExteriorWord k s c j) =
      fun R => ∑ i ∈ s, c i * exteriorWordDual G theta k q (j i) R := by
  funext R
  simp only [exteriorSeedDual,finiteExteriorWord,map_sum,map_smul,
    occupationInner_sum_right,occupationInner_smul_right,
    exteriorWordDual,actualExteriorWord]

theorem exteriorSeedDual_finiteWord_contDiff {I : Type*} (G : Geometry) (theta : Twist)
    (k : ℕ) (s : Finset I) (c : I → ℂ) (j : I → Fin k → ℕ)
    (q : Space (physicalQ G theta)) :
    ContDiff ℝ ∞ (exteriorSeedDual G theta q (finiteExteriorWord k s c j)) := by
  rw [exteriorSeedDual_finiteWord]
  apply ContDiff.sum
  intro i hi
  exact contDiff_const.mul (exteriorWordDual_contDiff G theta k q (j i))

theorem exteriorSeedDual_finiteWord_boundary {I : Type*} (G : Geometry) (theta : Twist)
    (k : ℕ) (s : Finset I) (c : I → ℂ) (j : I → Fin k → ℕ)
    (q : Space (physicalQ G theta)) :
    HasDualBoundary G theta k (exteriorSeedDual G theta q (finiteExteriorWord k s c j)) := by
  rw [exteriorSeedDual_finiteWord]
  exact ThermalCoherentSeedDomain.hasDualBoundary_finset_linear G theta k s c _
    (fun i _ => exteriorWordDual_boundary G theta k q (j i))

/-- Total orbital raise on the displayed alternating word representation. -/
def raiseExteriorWord (k : ℕ) (j : Fin k → ℕ) : FormalExterior :=
  ∑ a, (Real.sqrt (j a+1:ℝ):ℂ) • formalExteriorWord k (Function.update j a (j a+1))

/-- A zero label has zero lowering coefficient, without deleting the term. -/
def lowerExteriorWord (k : ℕ) (j : Fin k → ℕ) : FormalExterior :=
  ∑ a, (Real.sqrt (j a:ℝ):ℂ) • formalExteriorWord k (Function.update j a (j a-1))

theorem exteriorWordDual_raise_source (G : Geometry) (theta : Twist)
    (k : ℕ) [NeZero k] (q : Space (physicalQ G theta)) (j : Fin k → ℕ) (R : ℂ) :
    (Real.sqrt (k:ℝ):ℂ)*parameterRaise k (exteriorWordDual G theta k q j) R =
      exteriorSeedDual G theta q (raiseExteriorWord k j) R := by
  rw [exteriorWordDual_raise]
  simp only [exteriorSeedDual,raiseExteriorWord,map_sum,map_smul,
    occupationInner_sum_right,occupationInner_smul_right,
    exteriorWordDual,actualExteriorWord]

theorem exteriorWordDual_lower_source (G : Geometry) (theta : Twist)
    (k : ℕ) [NeZero k] (q : Space (physicalQ G theta)) (j : Fin k → ℕ) (R : ℂ) :
    (Real.sqrt (k:ℝ):ℂ)*parameterLower k (exteriorWordDual G theta k q j) R =
      exteriorSeedDual G theta q (lowerExteriorWord k j) R := by
  rw [exteriorWordDual_lower]
  simp only [exteriorSeedDual,lowerExteriorWord,map_sum,map_smul,
    occupationInner_sum_right,occupationInner_smul_right,
    exteriorWordDual,actualExteriorWord]

#print axioms exteriorSeedDual_finiteWord
#print axioms exteriorSeedDual_finiteWord_contDiff
#print axioms exteriorSeedDual_finiteWord_boundary
#print axioms exteriorWordDual_raise_source
#print axioms exteriorWordDual_lower_source

end TorusLean.Shared.ThermalCoherentFermionJetWord
