import torus.shared.PhysicalFermionExteriorSlater
import torus.shared.PhysicalFermionCAR

/-! All-N normalized equivalence from the actual full physical fermion carrier
to the genuine OAI exterior sector, measured in the original occupation inner product. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.PhysicalFermionExterior
open MeasureTheory
open scoped ComplexConjugate
open TorusLean.Shared.PhysicalNBodyCarrier TorusLean.Shared.PhysicalBosonSector
open TorusLean.Shared.PhysicalFermionCarrier TorusLean.Shared.PhysicalFermionCAR
open OAI.Laughlin.Fock

/-- Reindexing only; no physical or Fock completeness premise is supplied. -/
def physicalAlternatingEquiv (G : Geometry) (theta : Twist) (N : ℕ) :
    alternatingSpace (Fin (physicalQ G theta+1)) N ≃ₗ[ℂ] alternatingCoefficients G theta N where
  toFun c := ⟨fun w => c.val ((physicalIndexEquiv G theta).symm ∘ w), by
    intro σ w
    exact c.property σ ((physicalIndexEquiv G theta).symm ∘ w)⟩
  invFun c := ⟨fun w => c.val (physicalIndexEquiv G theta ∘ w), by
    intro σ w
    exact c.property σ (physicalIndexEquiv G theta ∘ w)⟩
  left_inv c := by
    apply Subtype.ext
    funext w
    simp [Function.comp_def]
  right_inv c := by
    apply Subtype.ext
    funext w
    simp [Function.comp_def]
  map_add' c d := rfl
  map_smul' a c := rfl

def physicalExteriorEquiv (G : Geometry) (theta : Twist) (N : ℕ) :
    Exterior (Fin (physicalQ G theta+1)) N ≃ PhysicalFermion G theta N :=
  (normalizedExteriorEquiv (Fin (physicalQ G theta+1)) N).toEquiv.trans
    ((physicalAlternatingEquiv G theta N).toEquiv.trans (physicalCoefficientEquiv G theta N))

lemma physicalExteriorEquiv_apply (G : Geometry) (theta : Twist) (N : ℕ)
    (x : Exterior (Fin (physicalQ G theta+1)) N) :
    (physicalExteriorEquiv G theta N x).val = tensorFunction G theta N
      (fun w => (normalizedExterior (Fin (physicalQ G theta+1)) N x).val
        ((physicalIndexEquiv G theta).symm ∘ w)) := rfl

/-- Underlying all-point wavefunction synthesis is genuinely linear. -/
def physicalExteriorLinear (G : Geometry) (theta : Twist) (N : ℕ) :
    Exterior (Fin (physicalQ G theta+1)) N →ₗ[ℂ] (Configuration N → ℂ) :=
  (tensorFunction G theta N).comp ((alternatingCoefficients G theta N).subtype.comp
    ((physicalAlternatingEquiv G theta N).toLinearMap.comp
      (normalizedExterior (Fin (physicalQ G theta+1)) N)))

lemma physicalExteriorEquiv_val_linear (G : Geometry) (theta : Twist) (N : ℕ)
    (x : Exterior (Fin (physicalQ G theta+1)) N) :
    (physicalExteriorEquiv G theta N x).val = physicalExteriorLinear G theta N x := rfl

theorem physicalExteriorEquiv_add (G : Geometry) (theta : Twist) (N : ℕ)
    (x y : Exterior (Fin (physicalQ G theta+1)) N) :
    (physicalExteriorEquiv G theta N (x+y)).val =
      (physicalExteriorEquiv G theta N x).val + (physicalExteriorEquiv G theta N y).val := by
  simp only [physicalExteriorEquiv_val_linear, map_add]

theorem physicalExteriorEquiv_smul (G : Geometry) (theta : Twist) (N : ℕ)
    (a : ℂ) (x : Exterior (Fin (physicalQ G theta+1)) N) :
    (physicalExteriorEquiv G theta N (a • x)).val = a • (physicalExteriorEquiv G theta N x).val := by
  simp only [physicalExteriorEquiv_val_linear, map_smul]

/-- The map is onto the independent full holomorphic, magnetic, antisymmetric
carrier, not a definition of the carrier as its image. -/
theorem physicalExteriorEquiv_surjective (G : Geometry) (theta : Twist) (N : ℕ) :
    Function.Surjective (physicalExteriorEquiv G theta N) :=
  (physicalExteriorEquiv G theta N).surjective

/-- The original product-cell integral and the official OAI occupation inner
product agree on all fixed-N states, with no N≤dimension hypothesis. -/
theorem physicalExteriorEquiv_inner (G : Geometry) (theta : Twist) (N : ℕ)
    (x y : Exterior (Fin (physicalQ G theta+1)) N) :
    sectorInner G N (physicalExteriorEquiv G theta N x).val
      (physicalExteriorEquiv G theta N y).val =
        occupationInner (physicalQ G theta) (x : Space (physicalQ G theta))
          (y : Space (physicalQ G theta)) := by
  rw [physicalExteriorEquiv_apply, physicalExteriorEquiv_apply, tensorFunction_inner]
  let e : Word G theta N ≃ (Fin N → Fin (physicalQ G theta+1)) := {
    toFun w := (physicalIndexEquiv G theta).symm ∘ w
    invFun w := physicalIndexEquiv G theta ∘ w
    left_inv w := by funext i; simp
    right_inv w := by funext i; simp }
  have hs := Equiv.sum_comp e
    (fun w => conj ((normalizedExterior (Fin (physicalQ G theta+1)) N x).val w) *
      (normalizedExterior (Fin (physicalQ G theta+1)) N y).val w)
  exact hs.trans (normalizedExterior_occupationInner x y)


/-- Parseval for every physical state in the original norm. -/
theorem physicalExteriorEquiv_normSq (G : Geometry) (theta : Twist) (N : ℕ)
    (x : Exterior (Fin (physicalQ G theta+1)) N) :
    (∫ z, ‖(physicalExteriorEquiv G theta N x).val z‖^2 ∂sectorMeasure G N) =
      occupationNormSq (physicalQ G theta) (x : Space (physicalQ G theta)) := by
  rw [← sectorInner_self_re, physicalExteriorEquiv_inner, occupationInner_self]
  exact Complex.ofReal_re _

/-- A canonical occupation has exactly one normalized Slater state. -/
theorem physicalSlater_gram (G : Geometry) (theta : Twist) (N : ℕ)
    (A B : Occupation (Fin (physicalQ G theta+1)) N) :
    sectorInner G N
      (physicalExteriorEquiv G theta N (exteriorBasis _ N A)).val
      (physicalExteriorEquiv G theta N (exteriorBasis _ N B)).val = if A = B then 1 else 0 := by
  rw [physicalExteriorEquiv_inner, ← normalizedExterior_occupationInner]
  exact normalizedSlater_gram A B

/-- Overfull physical states vanish as actual all-point functions. -/
theorem physicalExterior_zero_above_dimension (G : Geometry) (theta : Twist) (N : ℕ)
    (h : Module.finrank ℂ (LLL G theta 1) < N)
    (x : Exterior (Fin (physicalQ G theta+1)) N) :
    (physicalExteriorEquiv G theta N x).val = 0 :=
  physical_zero_above_dimension G theta N h _

/-- Actual ordered tensor coefficients of a synthesized exterior state. -/
theorem physicalExteriorEquiv_orderedCoefficient (G : Geometry) (theta : Twist) (N : ℕ)
    (x : Exterior (Fin (physicalQ G theta+1)) N) (w : Word G theta N) :
    ((physicalCoefficientEquiv G theta N).symm (physicalExteriorEquiv G theta N x)).val w =
      (normalizedExterior (Fin (physicalQ G theta+1)) N x).val
        ((physicalIndexEquiv G theta).symm ∘ w) := by
  change ((physicalCoefficientEquiv G theta N).symm
    (physicalCoefficientEquiv G theta N _)).val w = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- The inverse map has occupation coefficient √N! times the increasing
physical ordered coefficient, not the reciprocal scaling. -/
theorem physicalExteriorEquiv_inverse_occupation (G : Geometry) (theta : Twist) (N : ℕ)
    (f : PhysicalFermion G theta N) (A : Occupation (Fin (physicalQ G theta+1)) N) :
    (exteriorBasis (Fin (physicalQ G theta+1)) N).repr ((physicalExteriorEquiv G theta N).symm f) A =
      sqrtFactorial N * ((physicalCoefficientEquiv G theta N).symm f).val
        (physicalIndexEquiv G theta ∘ canonicalWord A) := by
  let x := (physicalExteriorEquiv G theta N).symm f
  have h := physicalExteriorEquiv_orderedCoefficient G theta N x
    (physicalIndexEquiv G theta ∘ canonicalWord A)
  rw [(physicalExteriorEquiv G theta N).apply_symm_apply] at h
  have he : (physicalIndexEquiv G theta).symm ∘ (physicalIndexEquiv G theta ∘ canonicalWord A) =
      canonicalWord A := by funext i; simp
  rw [he, normalizedExterior_canonical] at h
  rw [h, ← mul_assoc, mul_inv_cancel₀ (sqrtFactorial_ne_zero N), one_mul]

/-- The N=0 empty wedge is the constant vacuum wavefunction one. -/
theorem physicalExteriorEquiv_vacuum (G : Geometry) (theta : Twist) :
    (physicalExteriorEquiv G theta 0 (wedgeWord (Fin.elim0 : Fin 0 → Fin (physicalQ G theta+1)))).val =
      fun _ => 1 := by
  rw [physicalExteriorEquiv_apply]
  funext z
  simp [tensorFunction_apply, normalizedExterior_vacuum, wordFunction_zero]

/-- Both sides of an overfull sector vanish, including the genuine exterior
vector before its physical realization. -/
theorem physicalExterior_domain_zero_above_dimension (G : Geometry) (theta : Twist) (N : ℕ)
    (h : Module.finrank ℂ (LLL G theta 1) < N)
    (x : Exterior (Fin (physicalQ G theta+1)) N) : x = 0 := by
  apply exterior_zero_above_dimension _ x
  simpa only [Fintype.card_fin, physicalQ_succ] using h

#print axioms physicalExteriorEquiv_add
#print axioms physicalExteriorEquiv_smul
#print axioms physicalExteriorEquiv_orderedCoefficient
#print axioms physicalExteriorEquiv_inverse_occupation
#print axioms physicalExteriorEquiv_vacuum
#print axioms physicalExterior_domain_zero_above_dimension

#print axioms physicalExteriorEquiv_surjective
#print axioms physicalExteriorEquiv_inner
#print axioms physicalExteriorEquiv_normSq
#print axioms physicalSlater_gram
#print axioms physicalExterior_zero_above_dimension
end TorusLean.Shared.PhysicalFermionExterior
