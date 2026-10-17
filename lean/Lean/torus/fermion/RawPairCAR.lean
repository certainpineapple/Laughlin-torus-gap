import OAI.Analysis.Laughlin.Exterior.VectorAdjoint
import Mathlib.Tactic.NoncommRing

/-!
The nonorthogonal CAR calculation in paper eq:four-CAR.

`Orbital Q` here is the existing coordinate space with Q+1 orthonormal modes.
It is not a definition of the physical torus LLL.  An eventual unitary map from
`Shared.LLL` to this space transports raw torus jets into the arbitrary vectors
below.  No orthogonality, normalization, frame bound, or projection assumption
is imposed on those vectors.
-/

namespace TorusLean.Fermion

open OAI.Laughlin.Fock
open scoped BigOperators

noncomputable def rawCreate (Q : ℕ) (v : Orbital Q) : Module.End ℂ (Space Q) where
  toFun x := ExteriorAlgebra.ι ℂ v * x
  map_add' x y := mul_add _ x y
  map_smul' c x := by simp

/-- The existing orbital dual uses the first-variable-conjugate convention. -/
noncomputable def rawGram (Q : ℕ) (v w : Orbital Q) : ℂ := orbitalDual Q v w

noncomputable def rawPairCreate (Q : ℕ) (a b : Orbital Q) :
    Module.End ℂ (Space Q) := rawCreate Q a * rawCreate Q b

noncomputable def rawPairAnnihilate (Q : ℕ) (a b : Orbital Q) :
    Module.End ℂ (Space Q) := vectorAnnihilate Q b * vectorAnnihilate Q a

noncomputable def rawPairVector (Q : ℕ) (a b : Orbital Q) : Space Q :=
  rawPairCreate Q a b 1

noncomputable def rawPairGram (Q : ℕ) (a b c d : Orbital Q) : ℂ :=
  rawGram Q a c * rawGram Q b d - rawGram Q b c * rawGram Q a d

theorem rawGram_eq_sum (Q : ℕ) (v w : Orbital Q) :
    rawGram Q v w = ∑ i, star (v i) * w i := by
  simp [rawGram, orbitalDual, LinearMap.proj]

theorem raw_annihilate_create (Q : ℕ) (v w : Orbital Q) :
    vectorAnnihilate Q v * rawCreate Q w =
      rawGram Q v w • (1 : Module.End ℂ (Space Q)) -
        rawCreate Q w * vectorAnnihilate Q v := by
  apply LinearMap.ext
  intro x
  change CliffordAlgebra.contractLeft (orbitalDual Q v)
      (ExteriorAlgebra.ι ℂ w * x) =
    orbitalDual Q v w • x -
      ExteriorAlgebra.ι ℂ w * CliffordAlgebra.contractLeft (orbitalDual Q v) x
  exact CliffordAlgebra.contractLeft_ι_mul (Q := (0 : QuadraticForm ℂ (Orbital Q)))
    (d := orbitalDual Q v) w x

theorem raw_annihilate_vacuum (Q : ℕ) (v : Orbital Q) :
    vectorAnnihilate Q v (1 : Space Q) = 0 := by
  change CliffordAlgebra.contractLeft (orbitalDual Q v) (1 : Space Q) = 0
  exact CliffordAlgebra.contractLeft_one (Q := (0 : QuadraticForm ℂ (Orbital Q)))
    (d := orbitalDual Q v)

theorem rawCreate_adjoint (Q : ℕ) (v : Orbital Q) (x y : Space Q) :
    occupationInner Q (rawCreate Q v x) y =
      occupationInner Q x (vectorAnnihilate Q v y) :=
  vectorCreate_adjoint Q v x y

theorem rawPairCreate_adjoint (Q : ℕ) (a b : Orbital Q) (x y : Space Q) :
    occupationInner Q (rawPairCreate Q a b x) y =
      occupationInner Q x (rawPairAnnihilate Q a b y) := by
  simp only [rawPairCreate, rawPairAnnihilate, Module.End.mul_apply,
    rawCreate_adjoint]

theorem raw_normal_order_two_one (Q : ℕ) (a b d : Orbital Q) :
    vectorAnnihilate Q b * vectorAnnihilate Q a * rawCreate Q d =
      rawGram Q a d • vectorAnnihilate Q b -
        rawGram Q b d • vectorAnnihilate Q a +
        rawCreate Q d * vectorAnnihilate Q b * vectorAnnihilate Q a := by
  calc
    _ = vectorAnnihilate Q b *
        (vectorAnnihilate Q a * rawCreate Q d) := by noncomm_ring
    _ = rawGram Q a d • vectorAnnihilate Q b -
        (vectorAnnihilate Q b * rawCreate Q d) * vectorAnnihilate Q a := by
      rw [raw_annihilate_create]
      simp only [mul_sub, mul_smul_comm, mul_one]
      noncomm_ring
    _ = _ := by
      rw [raw_annihilate_create]
      simp only [sub_mul, smul_mul_assoc, one_mul]
      noncomm_ring

/-- Exact four single-contraction signs, valid for arbitrary raw orbitals. -/
theorem rawPair_normal_order (Q : ℕ) (a b c d : Orbital Q) :
    rawPairAnnihilate Q a b * rawPairCreate Q c d =
      rawPairGram Q a b c d • (1 : Module.End ℂ (Space Q)) -
      rawGram Q a c • (rawCreate Q d * vectorAnnihilate Q b) +
      rawGram Q b c • (rawCreate Q d * vectorAnnihilate Q a) +
      rawGram Q a d • (rawCreate Q c * vectorAnnihilate Q b) -
      rawGram Q b d • (rawCreate Q c * vectorAnnihilate Q a) +
      rawPairCreate Q c d * rawPairAnnihilate Q a b := by
  have hinner :
      vectorAnnihilate Q b * vectorAnnihilate Q a * rawCreate Q c * rawCreate Q d =
        rawGram Q a c • (vectorAnnihilate Q b * rawCreate Q d) -
        rawGram Q b c • (vectorAnnihilate Q a * rawCreate Q d) +
        rawCreate Q c * vectorAnnihilate Q b * vectorAnnihilate Q a * rawCreate Q d := by
    have ht := congrArg (fun A : Module.End ℂ (Space Q) => A * rawCreate Q d)
      (raw_normal_order_two_one Q a b c)
    simpa only [sub_mul, add_mul, smul_mul_assoc, mul_assoc] using ht
  unfold rawPairAnnihilate rawPairCreate
  rw [← mul_assoc, hinner, raw_annihilate_create Q b d,
    raw_annihilate_create Q a d]
  have h : rawCreate Q c * vectorAnnihilate Q b * vectorAnnihilate Q a * rawCreate Q d =
      rawCreate Q c * (vectorAnnihilate Q b * vectorAnnihilate Q a * rawCreate Q d) := by
    noncomm_ring
  rw [h, raw_normal_order_two_one]
  simp only [rawPairGram, smul_sub, smul_smul,
    mul_add, mul_sub, mul_smul_comm]
  module

/-- The double contraction is the pair Gram determinant, even when it is not one. -/
theorem rawPair_annihilate_vector (Q : ℕ) (a b c d : Orbital Q) :
    rawPairAnnihilate Q a b (rawPairVector Q c d) =
      rawPairGram Q a b c d • (1 : Space Q) := by
  have h := LinearMap.congr_fun (rawPair_normal_order Q a b c d) (1 : Space Q)
  simpa [rawPairVector, Module.End.mul_apply, rawPairAnnihilate,
    raw_annihilate_vacuum] using h

theorem occupationInner_vacuum (Q : ℕ) :
    occupationInner Q (1 : Space Q) 1 = 1 := by
  have hb : occupationBasis Q ∅ = (1 : Space Q) := by
    simp [occupationBasis, ExteriorAlgebra.basis_apply,
      ExteriorAlgebra.ιMulti_family]
    exact ExteriorAlgebra.ιMulti_zero_apply _
  rw [← hb]
  simp [occupationInner, Module.Basis.repr_self, Finsupp.single_apply]

/-- The determinant in CAR is exactly the physical exterior-pair inner product
after the pending unitary coordinate bridge; no Gram orthogonalization occurs. -/
theorem rawPairGram_eq_inner (Q : ℕ) (a b c d : Orbital Q) :
    rawPairGram Q a b c d =
      occupationInner Q (rawPairVector Q a b) (rawPairVector Q c d) := by
  rw [rawPairVector, rawPairCreate_adjoint, rawPair_annihilate_vector,
    occupationInner_smul_right, occupationInner_vacuum, mul_one]

/-- The paper's `v₀ = -u₀∧u₁` is represented by changing the first orbital's
sign.  This is a raw vector identity and does not renormalize a torus pair. -/
theorem rawPairVector_neg_left (Q : ℕ) (a b : Orbital Q) :
    rawPairVector Q (-a) b = -rawPairVector Q a b := by
  simp [rawPairVector, rawPairCreate, rawCreate, Module.End.mul_apply]

theorem rawGram_mode (Q : ℕ) (i j : Fin (Q + 1)) :
    rawGram Q (mode i) (mode j) = if i = j then 1 else 0 := by
  classical
  rw [rawGram_eq_sum]
  simp [mode, Pi.single_apply, eq_comm]

/-- An increasing Slater wedge of two orthonormal modes has norm one;
there is no additional factor of `2!` in the pair-vacuum convention. -/
theorem rawPairVector_mode_norm (Q : ℕ) (i j : Fin (Q + 1)) (different : i ≠ j) :
    occupationNormSq Q (rawPairVector Q (mode i) (mode j)) = 1 := by
  have h : occupationInner Q (rawPairVector Q (mode i) (mode j))
      (rawPairVector Q (mode i) (mode j)) = 1 := by
    rw [← rawPairGram_eq_inner]
    simp [rawPairGram, rawGram_mode, different, Ne.symm different]
  rw [occupationInner_self] at h
  exact_mod_cast h

#print axioms rawGram_eq_sum
#print axioms raw_annihilate_create
#print axioms raw_annihilate_vacuum
#print axioms rawCreate_adjoint
#print axioms rawPairCreate_adjoint
#print axioms raw_normal_order_two_one
#print axioms rawPair_normal_order
#print axioms rawPair_annihilate_vector
#print axioms occupationInner_vacuum
#print axioms rawPairGram_eq_inner
#print axioms rawPairVector_neg_left
#print axioms rawGram_mode
#print axioms rawPairVector_mode_norm

end TorusLean.Fermion
