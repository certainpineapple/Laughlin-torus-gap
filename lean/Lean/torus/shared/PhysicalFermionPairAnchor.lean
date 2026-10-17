import torus.shared.PhysicalFermionM1Contact
import Mathlib.GroupTheory.Perm.Fin

/-! The normalized actual m=1 pair anchor lands in the full physical spectator
fermion carrier. It is derived from literal contact and finite reconstruction;
it is not defined by transporting an exterior annihilator. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.PhysicalFermionPairAnchor

open MeasureTheory TorusLean.Geometry
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalFermionCarrier TorusLean.Shared.PhysicalFermionM1Contact
open TorusLean.Shared.PhysicalBosonDiagonal TorusLean.Shared.PhysicalBosonContactForm
open TorusLean.Shared.PhysicalBosonMembership TorusLean.Shared.LLLSliceReconstruction
open TorusLean.Shared.LLLTensorReconstruction

/-- The physical count normalization of one chosen pair, before exterior transport. -/
def pairAnchorScale (N : ℕ) : ℂ :=
  (Real.sqrt (((N+2 : ℕ) : ℝ) * (((N+2 : ℕ) : ℝ)-1) / 2) : ℂ)

/-- Literal original m=1 contact with the exact unordered-pair count. -/
def physicalM1PairFunction (N : ℕ) (R : ℂ) (f : Configuration (N+2) → ℂ)
    (y : Configuration N) : ℂ := pairAnchorScale N * m1Contact N f (R,y)

/-- Finite spectator coefficients of the actual, unnormalized contact. -/
def m1SpectatorCoefficients (G : Geometry) (theta : Twist) (N : ℕ) (R : ℂ)
    (c : Word G theta (N+2) → ℂ) (w : Word G theta N) : ℂ :=
  ∑ i, ∑ j, c (Fin.cons i (Fin.cons j w)) * pairM1 G theta i j R

theorem m1Contact_spectator_tensor (G : Geometry) (theta : Twist) (N : ℕ) (R : ℂ)
    (c : Word G theta (N+2) → ℂ) (y : Configuration N) :
    m1Contact N (tensorFunction G theta (N+2) c) (R,y) =
      tensorFunction G theta N (m1SpectatorCoefficients G theta N R c) y := by
  classical
  have ht (i j : OrbitalIndex G theta) (w : Word G theta N) :
      PhysicalBosonDiagonal.tailWord G theta N (Fin.cons i (Fin.cons j w)) = w := by
    funext k
    rfl
  rw [m1Contact_tensor, sum_words_succ]
  simp_rw [sum_words_succ]
  simp only [Fin.cons_zero, Fin.cons_one, ht]
  simp only [tensorFunction_apply, m1SpectatorCoefficients, Finset.sum_mul, ← mul_assoc]
  calc
    _ = ∑ i, ∑ w, ∑ j, c (Fin.cons i (Fin.cons j w)) * pairM1 G theta i j R *
        wordFunction G theta N w y := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Exact full spectator slice membership, without assuming derivative-output domains. -/
theorem fullCarrier_m1_has_slices (G : Geometry) (theta : Twist) (N : ℕ) (R : ℂ)
    (f : PhysicalFermion G theta (N+2)) :
    HasLLLSlices G theta N (fun y => m1Contact N f.val (R,y)) := by
  let c := ((physicalCoefficientEquiv G theta (N+2)).symm f).val
  have hf : tensorFunction G theta (N+2) c = f.val :=
    congrArg Subtype.val ((physicalCoefficientEquiv G theta (N+2)).apply_symm_apply f)
  have heq : (fun y => m1Contact N f.val (R,y)) =
      tensorFunction G theta N (m1SpectatorCoefficients G theta N R c) := by
    funext y
    rw [← hf, m1Contact_spectator_tensor]
  rw [heq]
  exact tensorFunction_has_slices G theta N _

/-- A real particle permutation fixing the two contact slots. -/
def liftSpectatorPermutation {N : ℕ} (σ : Equiv.Perm (Fin N)) : Equiv.Perm (Fin (N+2)) :=
  Equiv.Perm.decomposeFin.symm (0, Equiv.Perm.decomposeFin.symm (0,σ))

theorem liftSpectatorPermutation_sign {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    permutationSign (liftSpectatorPermutation σ) = permutationSign σ := by
  simp [permutationSign, liftSpectatorPermutation, Equiv.Perm.decomposeFin.symm_sign]

theorem insertPair_spectator_permutation (N : ℕ) (y : Configuration N) (p : ℂ × ℂ)
    (σ : Equiv.Perm (Fin N)) :
    insertPair N (y ∘ σ) p = insertPair N y p ∘ liftSpectatorPermutation σ := by
  funext k
  refine Fin.cases ?_ (fun k => Fin.cases ?_ ?_ k) k
  · simp [insertPair, liftSpectatorPermutation]
  · simp [insertPair, liftSpectatorPermutation]
  · intro k
    simp [insertPair, liftSpectatorPermutation, Function.comp_def]

theorem fullCarrier_m1_antisymmetric (G : Geometry) (theta : Twist) (N : ℕ) (R : ℂ)
    (f : PhysicalFermion G theta (N+2)) :
    FermionAntisymmetric N (fun y => m1Contact N f.val (R,y)) := by
  intro σ y
  have heq : (fun p : ℂ × ℂ => f.val (insertPair N (y ∘ σ) p)) =
      (fun p => permutationSign σ * f.val (insertPair N y p)) := by
    funext p
    rw [insertPair_spectator_permutation, f.property.2.2, liftSpectatorPermutation_sign]
  dsimp only [m1Contact]
  rw [heq]
  exact m1Contact_const_mul N (permutationSign σ) f.val (R,y)

/-- The original derivative output is a complete physical spectator state. -/
def m1Section (G : Geometry) (theta : Twist) (N : ℕ) (R : ℂ)
    (f : PhysicalFermion G theta (N+2)) : PhysicalFermion G theta N :=
  ⟨fun y => m1Contact N f.val (R,y),
    (slices_iff_joint_and_boundary G theta N _).mp (fullCarrier_m1_has_slices G theta N R f) |>.1,
    (slices_iff_joint_and_boundary G theta N _).mp (fullCarrier_m1_has_slices G theta N R f) |>.2,
    fullCarrier_m1_antisymmetric G theta N R f⟩

/-- The normalized physical pair anchor has the same full-carrier membership. -/
def physicalM1PairSection (G : Geometry) (theta : Twist) (N : ℕ) (R : ℂ)
    (f : PhysicalFermion G theta (N+2)) : PhysicalFermion G theta N := by
  have hs : HasLLLSlices G theta N (physicalM1PairFunction N R f.val) := by
    change (pairAnchorScale N • (fun y => m1Contact N f.val (R,y))) ∈ sliceSubmodule G theta N
    exact (sliceSubmodule G theta N).smul_mem (pairAnchorScale N)
      (fullCarrier_m1_has_slices G theta N R f)
  refine ⟨physicalM1PairFunction N R f.val,
    ((slices_iff_joint_and_boundary G theta N _).mp hs).1,
    ((slices_iff_joint_and_boundary G theta N _).mp hs).2, ?_⟩
  intro σ y
  simp only [physicalM1PairFunction]
  have h := fullCarrier_m1_antisymmetric G theta N R f σ y
  change m1Contact N f.val (R,y ∘ σ) = permutationSign σ * m1Contact N f.val (R,y) at h
  rw [h]
  ring

@[simp] theorem m1Section_apply (G : Geometry) (theta : Twist) (N : ℕ) (R : ℂ)
    (f : PhysicalFermion G theta (N+2)) (y : Configuration N) :
    (m1Section G theta N R f).val y = m1Contact N f.val (R,y) := rfl

@[simp] theorem physicalM1PairSection_apply (G : Geometry) (theta : Twist) (N : ℕ) (R : ℂ)
    (f : PhysicalFermion G theta (N+2)) (y : Configuration N) :
    (physicalM1PairSection G theta N R f).val y = physicalM1PairFunction N R f.val y := rfl

theorem pairAnchorScale_normSq (N : ℕ) :
    ‖pairAnchorScale N‖^2 = ((N+2 : ℕ) : ℝ) * (((N+2 : ℕ) : ℝ)-1) / 2 := by
  have hp : 0 ≤ ((N+2 : ℕ) : ℝ) * (((N+2 : ℕ) : ℝ)-1) / 2 := by
    have hN : (0:ℝ) ≤ N := Nat.cast_nonneg N
    push_cast
    apply le_of_lt
    exact div_pos (mul_pos (by positivity) (by linarith)) (by norm_num)
  simp only [pairAnchorScale, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hp]

/-- Actual pair-anchor norm in the unchanged spectator/COM product measure. -/
theorem physicalM1Pair_anchor_energy (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta (N+2)) :
    (∫ R, (∫ y, ‖physicalM1PairFunction N R f.val y‖^2 ∂sectorMeasure G N)
      ∂cellMeasure G 2) = actualFermionM1Energy G (N+2) f.val := by
  simp only [physicalM1PairFunction, norm_mul, mul_pow, pairAnchorScale_normSq]
  simp_rw [integral_const_mul]
  change _ = particleM1Energy G N f.val
  rw [fullCarrier_particleM1Energy]
  congr 1
  exact (integral_prod _ (fullCarrier_m1_normSq_integrable G theta N f)).symm

#print axioms m1Contact_spectator_tensor
#print axioms fullCarrier_m1_has_slices
#print axioms liftSpectatorPermutation_sign
#print axioms insertPair_spectator_permutation
#print axioms fullCarrier_m1_antisymmetric
#print axioms m1Section_apply
#print axioms physicalM1PairSection_apply
#print axioms pairAnchorScale_normSq
#print axioms physicalM1Pair_anchor_energy

end TorusLean.Shared.PhysicalFermionPairAnchor
