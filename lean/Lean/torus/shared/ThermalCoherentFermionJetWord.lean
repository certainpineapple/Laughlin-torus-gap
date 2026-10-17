import torus.shared.FermionLocalJetFourCouplingWedge
import torus.shared.ParameterRawJetWord
import torus.shared.ThermalCoherentSeedDomain

/-! Actual alternating jet words and their finite scalar parameter expansion.
The source is the existing Nat exterior algebra; the map is the actual raw
jet exterior map. Multilinearity preserves order and all zero repeated-mode
words. No symmetric polynomial substitution or exterior isometry is used. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionJetWord
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.ParameterRawJetLadder TorusLean.Shared.ParameterRawJetWord
open TorusLean.Shared.ParameterCellAdjoint
open scoped BigOperators ContDiff

/-- Ordered finite exterior word, including the empty word and repeated zeros. -/
def formalExteriorWord (k : ℕ) (j : Fin k → ℕ) : FormalExterior :=
  ExteriorAlgebra.ιMulti ℂ k (fun a => Finsupp.single (j a) 1)

def coordinateExteriorWord (Q k : ℕ) (w : Fin k → Fin (Q+1)) : Space Q :=
  ExteriorAlgebra.ιMulti ℂ k (fun a => mode (w a))

def actualExteriorWord (G : Geometry) (theta : Twist) (k : ℕ)
    (j : Fin k → ℕ) (R : ℂ) : Space (physicalQ G theta) :=
  rawJetExteriorMap G theta R (formalExteriorWord k j)

/-- True functoriality of the existing exterior map, with no commutative replacement. -/
theorem actualExteriorWord_eq (G : Geometry) (theta : Twist) (k : ℕ)
    (j : Fin k → ℕ) (R : ℂ) :
    actualExteriorWord G theta k j R =
      ExteriorAlgebra.ιMulti ℂ k (fun a => physicalJetCoordinates G theta (j a) R) := by
  simp only [actualExteriorWord, formalExteriorWord, rawJetExteriorMap,
    ExteriorAlgebra.map_apply_ιMulti]
  apply congrArg (ExteriorAlgebra.ιMulti ℂ k)
  funext a
  simp only [Function.comp_apply, rawJetOrbitalMap,
    Finsupp.linearCombination_single, one_smul]

/-- The genuine alternating multilinear expansion keeps all ordered assignments.
Repeated orbital assignments vanish in the exterior word itself. -/
theorem exteriorWord_coordinate_expansion (Q k : ℕ) (u : Fin k → Orbital Q) :
    ExteriorAlgebra.ιMulti ℂ k u =
      ∑ w : Fin k → Fin (Q+1), (∏ a, u a (w a)) • coordinateExteriorWord Q k w := by
  classical
  have hu (a : Fin k) : u a=∑ i, u a i • mode i := by
    funext i
    simp [mode,Pi.single_apply]
  calc
    _ = (ExteriorAlgebra.ιMulti ℂ k).toMultilinearMap
        (fun a => ∑ i, u a i • mode i) := congrArg _ (funext hu)
    _ = ∑ w : Fin k → Fin (Q+1),
        (ExteriorAlgebra.ιMulti ℂ k).toMultilinearMap (fun a => u a (w a) • mode (w a)) :=
      MultilinearMap.map_sum _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w hw
      exact MultilinearMap.map_smul_univ _ _ _

theorem physicalJetCoordinates_eq_dualRaw (G : Geometry) (theta : Twist)
    (j : ℕ) (R : ℂ) (i : Fin (physicalQ G theta+1)) :
    physicalJetCoordinates G theta j R i =
      dualRawJetScalar G theta (orbitalBasis G theta (physicalIndexEquiv G theta i)) j R := by
  rw [physicalJetCoordinates,physicalOrbitalCoordinates_apply]
  rfl

/-- Fixed test core in the first slot; the finite coefficient has no conjugation. -/
def exteriorWordDual (G : Geometry) (theta : Twist) (k : ℕ)
    (q : Space (physicalQ G theta)) (j : Fin k → ℕ) (R : ℂ) : ℂ :=
  occupationInner (physicalQ G theta) q (actualExteriorWord G theta k j R)

theorem exteriorWordDual_expansion (G : Geometry) (theta : Twist) (k : ℕ)
    (q : Space (physicalQ G theta)) (j : Fin k → ℕ) :
    exteriorWordDual G theta k q j = fun R =>
      ∑ w : Fin k → Fin (physicalQ G theta+1),
        occupationInner (physicalQ G theta) q (coordinateExteriorWord (physicalQ G theta) k w) *
          rawWord G theta k
            (fun a => orbitalBasis G theta (physicalIndexEquiv G theta (w a))) j R := by
  funext R
  rw [exteriorWordDual,actualExteriorWord_eq,exteriorWord_coordinate_expansion]
  simp only [occupationInner_sum_right,occupationInner_smul_right,
    physicalJetCoordinates_eq_dualRaw,rawWord,mul_comm]

theorem exteriorWordDual_contDiff (G : Geometry) (theta : Twist) (k : ℕ)
    (q : Space (physicalQ G theta)) (j : Fin k → ℕ) :
    ContDiff ℝ ∞ (exteriorWordDual G theta k q j) := by
  rw [exteriorWordDual_expansion]
  apply ContDiff.sum
  intro w hw
  exact contDiff_const.mul (rawWord_contDiff G theta k _ _)

theorem exteriorWordDual_boundary (G : Geometry) (theta : Twist) (k : ℕ)
    (q : Space (physicalQ G theta)) (j : Fin k → ℕ) :
    HasDualBoundary G theta k (exteriorWordDual G theta k q j) := by
  rw [exteriorWordDual_expansion]
  exact ThermalCoherentSeedDomain.hasDualBoundary_finset_linear G theta k Finset.univ _ _
    (fun w _ => rawWord_hasDualBoundary G theta k _ _)

#print axioms actualExteriorWord_eq
#print axioms exteriorWord_coordinate_expansion
#print axioms physicalJetCoordinates_eq_dualRaw
#print axioms exteriorWordDual_expansion
#print axioms exteriorWordDual_contDiff
#print axioms exteriorWordDual_boundary

end TorusLean.Shared.ThermalCoherentFermionJetWord
