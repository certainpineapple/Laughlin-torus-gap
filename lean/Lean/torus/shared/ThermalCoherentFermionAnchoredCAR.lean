import torus.fermion.RawPairCAR
import Mathlib.Tactic.Module

/-! Finite exterior source identities for the anchored fermion kernel.
These use the original OAI CAR exterior algebra and its occupation metric.
The ordered pair half is displayed explicitly; antisymmetry, rather than an
orthogonality assumption on physical jets, reconciles it with pair creation.
No plane Hamiltonian, COM trace, or physical S3 identity is assumed here. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFermionAnchored
open OAI.Laughlin.Fock TorusLean.Fermion
open scoped BigOperators ComplexConjugate

/-- The genuine exterior product in the stated left-to-right order. -/
def rawTripleVector (Q : ℕ) (a b c : Orbital Q) : Space Q :=
  rawCreate Q a (rawCreate Q b (rawCreate Q c 1))

/-- The ordered pair coefficient convention: the half counts both orders. -/
def coefficientPairCreate (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ) :
    Module.End ℂ (Space Q) :=
  (1/2:ℂ) • ∑ i, ∑ j, c i j • rawPairCreate Q (mode i) (mode j)

/-- The actual conjugate-linear adjoint row of that pair creator. -/
def coefficientPairRemove (Q : ℕ) (c : Fin (Q+1) → Fin (Q+1) → ℂ) :
    Module.End ℂ (Space Q) :=
  (1/2:ℂ) • ∑ i, ∑ j, conj (c i j) • rawPairAnnihilate Q (mode i) (mode j)

theorem raw_annihilate_create_apply (Q : ℕ) (a b : Orbital Q) (x : Space Q) :
    vectorAnnihilate Q a (rawCreate Q b x) =
      rawGram Q a b • x - rawCreate Q b (vectorAnnihilate Q a x) := by
  exact LinearMap.congr_fun (raw_annihilate_create Q a b) x

/-- All three two-fold contractions with their original exterior signs.
This holds for arbitrary raw orbitals, including nonorthogonal/repeated ones. -/
theorem rawPairAnnihilate_tripleVector (Q : ℕ) (a b c d e : Orbital Q) :
    rawPairAnnihilate Q a b (rawTripleVector Q c d e) =
      rawPairGram Q a b c d • rawCreate Q e 1 -
      rawPairGram Q a b c e • rawCreate Q d 1 +
      rawPairGram Q a b d e • rawCreate Q c 1 := by
  simp only [rawPairAnnihilate,Module.End.mul_apply,rawTripleVector,
    raw_annihilate_create_apply,raw_annihilate_vacuum,map_zero,sub_zero,
    map_smul,map_sub,smul_sub,smul_smul,rawPairGram]
  module

/-- The l=0 anchored triple is literally zero in the original exterior algebra. -/
theorem rawTripleVector_repeat_first (Q : ℕ) (a b : Orbital Q) :
    rawTripleVector Q a b a=0 := by
  simp only [rawTripleVector,rawCreate,LinearMap.coe_mk,AddHom.coe_mk,mul_one]
  have hs : ExteriorAlgebra.ι ℂ b * ExteriorAlgebra.ι ℂ a =
      -(ExteriorAlgebra.ι ℂ a * ExteriorAlgebra.ι ℂ b) :=
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap b a)
  rw [hs,mul_neg,← mul_assoc,ExteriorAlgebra.ι_sq_zero,zero_mul,neg_zero]

/-- The l=1 anchored triple is likewise zero, before any normalization. -/
theorem rawTripleVector_repeat_second (Q : ℕ) (a b : Orbital Q) :
    rawTripleVector Q a b b=0 := by
  simp only [rawTripleVector,rawCreate,LinearMap.coe_mk,AddHom.coe_mk,mul_one,
    ExteriorAlgebra.ι_sq_zero,mul_zero]

private theorem coefficient_pair_gram (Q : ℕ)
    (c : Fin (Q+1) → Fin (Q+1) → ℂ) (a b : Fin (Q+1)) :
    (∑ i, ∑ j, conj (c i j) * rawPairGram Q (mode i) (mode j) (mode a) (mode b)) =
      conj (c a b) - conj (c b a) := by
  classical
  simp [rawPairGram,rawGram_mode,mul_sub,Finset.sum_sub_distrib,mul_ite,eq_comm]

/-- True pair removal on an ordered three-mode wedge. The six CAR terms
combine in pairs; their ordered half cancels once and only once. -/
theorem coefficientPairRemove_tripleVector (Q : ℕ)
    (c : Fin (Q+1) → Fin (Q+1) → ℂ) (hc : ∀ i j, c j i = -c i j)
    (a b d : Fin (Q+1)) :
    coefficientPairRemove Q c (rawTripleVector Q (mode a) (mode b) (mode d)) =
      conj (c a b) • rawCreate Q (mode d) 1 -
      conj (c a d) • rawCreate Q (mode b) 1 +
      conj (c b d) • rawCreate Q (mode a) 1 := by
  simp only [coefficientPairRemove,LinearMap.smul_apply,LinearMap.sum_apply,
    rawPairAnnihilate_tripleVector,smul_add,smul_sub,smul_smul,
    Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.sum_smul]
  rw [coefficient_pair_gram,coefficient_pair_gram,coefficient_pair_gram]
  rw [hc a b,hc a d,hc b d]
  simp only [map_neg]
  module

/-- The creator/remover definitions are actual occupation adjoints on every
finite exterior state, without a fixed particle-number premise. -/
theorem coefficientPairCreate_adjoint (Q : ℕ)
    (c : Fin (Q+1) → Fin (Q+1) → ℂ) (x y : Space Q) :
    occupationInner Q (coefficientPairCreate Q c x) y =
      occupationInner Q x (coefficientPairRemove Q c y) := by
  have hc : conj (1/2:ℂ)=(1/2:ℂ) := by
    simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using
      Complex.conj_ofReal (1/2:ℝ)
  simp only [coefficientPairCreate,coefficientPairRemove,LinearMap.smul_apply,
    LinearMap.sum_apply,occupationInner_sum_left,occupationInner_sum_right,
    occupationInner_smul_left,occupationInner_smul_right,rawPairCreate_adjoint,
    Complex.star_def,hc]

end TorusLean.Shared.ThermalCoherentFermionAnchored
