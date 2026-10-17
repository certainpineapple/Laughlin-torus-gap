import torus.shared.ThermalCoherentFermionJetWordDomain

/-! Finite homogeneous exterior sources, with the actual raw-jet exterior map.
The fixed length k is particle number and magnetic charge, not orbital degree.
All labels are Nat. No polynomial aeval, Gram inverse, or isometry is used. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionJetWord
open TorusLean.Geometry TorusLean.Fermion OAI.Laughlin.Fock
open TorusLean.Shared.PhysicalFermionCAR
open TorusLean.Shared.FermionLocalJet.FourCoupling
open TorusLean.Shared.ParameterCellAdjoint TorusLean.Shared.ParameterRawJetLadder
open TorusLean.Shared.BosonAnchoredSeedActions
open scoped BigOperators ContDiff

/-- Linear analysis of the actual exterior image, in the source slot. -/
def exteriorSeedDualLinearMap (G : Geometry) (theta : Twist)
    (q : Space (physicalQ G theta)) : FormalExterior →ₗ[ℂ] (ℂ → ℂ) where
  toFun := exteriorSeedDual G theta q
  map_add' v w := by
    funext R
    simp [exteriorSeedDual, occupationInner, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    funext R
    simp only [exteriorSeedDual, map_smul, occupationInner_smul_right,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

theorem exteriorSeedDualLinearMap_word (G : Geometry) (theta : Twist)
    (q : Space (physicalQ G theta)) (k : ℕ) (j : Fin k → ℕ) :
    exteriorSeedDualLinearMap G theta q (formalExteriorWord k j) =
      exteriorWordDual G theta k q j := rfl

/-- Exterior antisymmetry is retained before any coordinate expansion. -/
theorem formalExteriorWord_swap (k : ℕ) (j : Fin k → ℕ)
    (a b : Fin k) (hab : a ≠ b) :
    formalExteriorWord k (j ∘ Equiv.swap a b) = -formalExteriorWord k j := by
  unfold formalExteriorWord
  calc
    _ = (ExteriorAlgebra.ιMulti ℂ k)
        ((fun i => Finsupp.single (j i) (1 : ℂ)) ∘ Equiv.swap a b) := by
      apply congrArg (ExteriorAlgebra.ιMulti ℂ k)
      funext i
      rfl
    _ = _ := (ExteriorAlgebra.ιMulti ℂ k).map_swap
      (fun i => Finsupp.single (j i) (1 : ℂ)) hab

theorem formalExteriorWord_repeat (k : ℕ) (j : Fin k → ℕ)
    (a b : Fin k) (hab : a ≠ b) (hj : j a = j b) :
    formalExteriorWord k j = 0 := by
  exact (ExteriorAlgebra.ιMulti ℂ k).map_eq_zero_of_eq _
    (congrArg (fun n : ℕ => Finsupp.single n (1 : ℂ)) hj) hab

theorem actualExteriorWord_swap (G : Geometry) (theta : Twist)
    (k : ℕ) (j : Fin k → ℕ) (a b : Fin k) (hab : a ≠ b) (R : ℂ) :
    actualExteriorWord G theta k (j ∘ Equiv.swap a b) R =
      -actualExteriorWord G theta k j R := by
  rw [actualExteriorWord, formalExteriorWord_swap k j a b hab, map_neg]
  rfl

theorem actualExteriorWord_repeat (G : Geometry) (theta : Twist)
    (k : ℕ) (j : Fin k → ℕ) (a b : Fin k) (hab : a ≠ b)
    (hj : j a = j b) (R : ℂ) : actualExteriorWord G theta k j R = 0 := by
  rw [actualExteriorWord, formalExteriorWord_repeat k j a b hab hj, map_zero]

@[simp] theorem formalExteriorWord_zero (j : Fin 0 → ℕ) :
    formalExteriorWord 0 j = 1 := by
  simp only [formalExteriorWord, ExteriorAlgebra.ιMulti_zero_apply]

@[simp] theorem actualExteriorWord_zero (G : Geometry) (theta : Twist)
    (j : Fin 0 → ℕ) (R : ℂ) : actualExteriorWord G theta 0 j R = 1 := by
  rw [actualExteriorWord, formalExteriorWord_zero, map_one]

/-- Charge zero is handled explicitly, never by a nonexistent NeZero instance. -/
@[simp] theorem exteriorWordDual_zero (G : Geometry) (theta : Twist)
    (q : Space (physicalQ G theta)) (j : Fin 0 → ℕ) :
    exteriorWordDual G theta 0 q j = fun _ => occupationInner (physicalQ G theta) q 1 := by
  funext R
  simp only [exteriorWordDual, actualExteriorWord_zero]

@[simp] theorem parameterRaise_charge_zero (f : ℂ → ℂ) : parameterRaise 0 f = 0 := by
  funext R
  simp [parameterRaise]

@[simp] theorem parameterLower_charge_zero (f : ℂ → ℂ) : parameterLower 0 f = 0 := by
  funext R
  simp [parameterLower]

def raiseFiniteExteriorWord {I : Type*} (k : ℕ) (s : Finset I)
    (c : I → ℂ) (j : I → Fin k → ℕ) : FormalExterior :=
  ∑ i ∈ s, c i • raiseExteriorWord k (j i)

def lowerFiniteExteriorWord {I : Type*} (k : ℕ) (s : Finset I)
    (c : I → ℂ) (j : I → Fin k → ℕ) : FormalExterior :=
  ∑ i ∈ s, c i • lowerExteriorWord k (j i)

/-- A label zero contributes the literal zero term; Nat subtraction is harmless. -/
theorem lowerExteriorWord_term_zero (k : ℕ) (j : Fin k → ℕ)
    (a : Fin k) (ha : j a = 0) :
    (Real.sqrt (j a : ℝ) : ℂ) •
      formalExteriorWord k (Function.update j a (j a - 1)) = 0 := by
  simp [ha]

/-- The genuine charge-k raising operator, for every finite exterior linear sum. -/
theorem exteriorSeedDual_finiteWord_raise {I : Type*} (G : Geometry) (theta : Twist)
    (k : ℕ) [NeZero k] (q : Space (physicalQ G theta))
    (s : Finset I) (c : I → ℂ) (j : I → Fin k → ℕ) (R : ℂ) :
    (Real.sqrt (k : ℝ) : ℂ) * parameterRaise k
      (exteriorSeedDual G theta q (finiteExteriorWord k s c j)) R =
      exteriorSeedDual G theta q (raiseFiniteExteriorWord k s c j) R := by
  have hf (i : I) : Differentiable ℝ (exteriorWordDual G theta k q (j i)) :=
    (exteriorWordDual_contDiff G theta k q (j i)).differentiable (by simp)
  change (Real.sqrt (k : ℝ) : ℂ) * parameterRaise k
    (exteriorSeedDualLinearMap G theta q (finiteExteriorWord k s c j)) R =
    exteriorSeedDualLinearMap G theta q (raiseFiniteExteriorWord k s c j) R
  simp only [finiteExteriorWord, raiseFiniteExteriorWord, raiseExteriorWord,
    map_sum, map_smul, exteriorSeedDualLinearMap_word]
  have hsum : (∑ i ∈ s, c i • exteriorWordDual G theta k q (j i)) =
      (fun z => ∑ i ∈ s, c i * exteriorWordDual G theta k q (j i) z) := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsum]
  rw [parameterRaise_sum _ _ _ (fun i _ => (hf i).const_mul _), Finset.mul_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [parameterRaise_const_mul k _ _ (hf i)]
  calc
    _ = c i * ((Real.sqrt (k : ℝ) : ℂ) *
        parameterRaise k (exteriorWordDual G theta k q (j i)) R) := by ring
    _ = _ := by rw [exteriorWordDual_raise G theta k q (j i) R]

/-- The genuine charge-k lowering operator, retaining every zero-label term. -/
theorem exteriorSeedDual_finiteWord_lower {I : Type*} (G : Geometry) (theta : Twist)
    (k : ℕ) [NeZero k] (q : Space (physicalQ G theta))
    (s : Finset I) (c : I → ℂ) (j : I → Fin k → ℕ) (R : ℂ) :
    (Real.sqrt (k : ℝ) : ℂ) * parameterLower k
      (exteriorSeedDual G theta q (finiteExteriorWord k s c j)) R =
      exteriorSeedDual G theta q (lowerFiniteExteriorWord k s c j) R := by
  have hf (i : I) : Differentiable ℝ (exteriorWordDual G theta k q (j i)) :=
    (exteriorWordDual_contDiff G theta k q (j i)).differentiable (by simp)
  change (Real.sqrt (k : ℝ) : ℂ) * parameterLower k
    (exteriorSeedDualLinearMap G theta q (finiteExteriorWord k s c j)) R =
    exteriorSeedDualLinearMap G theta q (lowerFiniteExteriorWord k s c j) R
  simp only [finiteExteriorWord, lowerFiniteExteriorWord, lowerExteriorWord,
    map_sum, map_smul, exteriorSeedDualLinearMap_word]
  have hsum : (∑ i ∈ s, c i • exteriorWordDual G theta k q (j i)) =
      (fun z => ∑ i ∈ s, c i * exteriorWordDual G theta k q (j i) z) := by
    funext z
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsum]
  rw [parameterLower_sum _ _ _ (fun i _ => (hf i).const_mul _), Finset.mul_sum]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [parameterLower_const_mul k _ _ (hf i)]
  calc
    _ = c i * ((Real.sqrt (k : ℝ) : ℂ) *
        parameterLower k (exteriorWordDual G theta k q (j i)) R) := by ring
    _ = _ := by rw [exteriorWordDual_lower G theta k q (j i) R]

#print axioms exteriorSeedDual_finiteWord_raise
#print axioms exteriorSeedDual_finiteWord_lower
#print axioms actualExteriorWord_swap
#print axioms actualExteriorWord_repeat
#print axioms exteriorSeedDualLinearMap_word
#print axioms formalExteriorWord_swap
#print axioms formalExteriorWord_repeat
#print axioms formalExteriorWord_zero
#print axioms actualExteriorWord_zero
#print axioms exteriorWordDual_zero
#print axioms parameterRaise_charge_zero
#print axioms parameterLower_charge_zero
#print axioms lowerExteriorWord_term_zero

end TorusLean.Shared.ThermalCoherentFermionJetWord
