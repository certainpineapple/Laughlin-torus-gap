import torus.shared.BosonNatFourCOMOccupationCross
import torus.shared.BosonFiniteCertificateNatFourCOMDualCore
import Mathlib.Data.Matrix.Block

/-! The complete COM family's Gram is a genuine block diagonal Gram, with
one original relative Gram for each relative degree and the exact ladder
factor 4^n n!. Its inverse is built from the small relative inverses. The
index includes every fiber, including the empty degree-one relative fiber.
No large unconstrained inverse or relative-only spanning claim is used. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonNatFourCOMOccupationCross
open Matrix
open scoped BigOperators

def natFourCOMWeight (n : ℕ) : ℂ := (4 : ℂ)^n*(n.factorial : ℂ)

theorem natFourCOMWeight_ne_zero (n : ℕ) : natFourCOMWeight n ≠ 0 := by
  unfold natFourCOMWeight
  exact mul_ne_zero (pow_ne_zero n (by norm_num))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))

def natFourCOMSigmaFamily (D : ℕ) (dim : Fin (D+1) → ℕ)
    (u : ∀ d, Fin (dim d) → Core ℕ ℂ)
    (a : Σ d, Fin (dim d)) : Core ℕ ℂ :=
  ((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[D-a.1.val]) (u a.1 a.2)

def natFourCOMBlockGram (D : ℕ) (dim : Fin (D+1) → ℕ)
    (F : ∀ d, Matrix (Fin (dim d)) (Fin (dim d)) ℂ) :
    Matrix (Σ d, Fin (dim d)) (Σ d, Fin (dim d)) ℂ :=
  Matrix.blockDiagonal' fun d => natFourCOMWeight (D-d.val) • F d

def natFourCOMBlockInverse (D : ℕ) (dim : Fin (D+1) → ℕ)
    (J : ∀ d, Matrix (Fin (dim d)) (Fin (dim d)) ℂ) :
    Matrix (Σ d, Fin (dim d)) (Σ d, Fin (dim d)) ℂ :=
  Matrix.blockDiagonal' fun d => (natFourCOMWeight (D-d.val))⁻¹ • J d

/-- This is an identity of the actual occupation inner products. Relative
columns need not be orthogonal, normalized, or linearly independent. -/
theorem natFourCOMSigmaFamily_gram (D : ℕ) (dim : Fin (D+1) → ℕ)
    (u : ∀ d, Fin (dim d) → Core ℕ ℂ)
    (F : ∀ d, Matrix (Fin (dim d)) (Fin (dim d)) ℂ)
    (hN : ∀ d a, (u d a).IsHomogeneous 4)
    (hL : ∀ d a, canonicalCOMLowerNat (u d a)=0)
    (hF : ∀ d, natFamilyGram (u d)=F d) :
    (fun a b => natOccupationInner (natFourCOMSigmaFamily D dim u a)
      (natFourCOMSigmaFamily D dim u b))=natFourCOMBlockGram D dim F := by
  ext ⟨d,a⟩ ⟨e,b⟩
  change natOccupationInner
    (((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[D-d.val]) (u d a))
    (((canonicalCOMRaiseNat : Core ℕ ℂ → Core ℕ ℂ)^[D-e.val]) (u e b)) = _
  rw [natFour_COM_iterate_cross _ _ _ _ (hN e b) (hL d a) (hL e b)]
  by_cases h : d=e
  · subst e
    rw [if_pos rfl]
    change natFourCOMWeight (D-d.val)*natFamilyGram (u d) a b =
      Matrix.blockDiagonal' (fun z => natFourCOMWeight (D-z.val) • F z) ⟨d,a⟩ ⟨d,b⟩
    rw [hF,Matrix.blockDiagonal'_apply_eq]
    rfl
  · have hlevel : D-d.val ≠ D-e.val := by
      intro heq
      apply h
      apply Fin.ext
      have hd := d.isLt
      have he := e.isLt
      omega
    rw [if_neg hlevel]
    exact (Matrix.blockDiagonal'_apply_ne
      (fun z => natFourCOMWeight (D-z.val) • F z) a b h).symm

theorem natFourCOMBlockInverse_left (D : ℕ) (dim : Fin (D+1) → ℕ)
    (F J : ∀ d, Matrix (Fin (dim d)) (Fin (dim d)) ℂ)
    (hJF : ∀ d, J d*F d=1) :
    natFourCOMBlockInverse D dim J*natFourCOMBlockGram D dim F=1 := by
  unfold natFourCOMBlockInverse natFourCOMBlockGram
  rw [←Matrix.blockDiagonal'_mul]
  have h : (fun d => (natFourCOMWeight (D-d.val))⁻¹ • J d *
      (natFourCOMWeight (D-d.val) • F d)) = (1 : ∀ d, Matrix (Fin (dim d)) (Fin (dim d)) ℂ) := by
    funext d
    rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,inv_mul_cancel₀ (natFourCOMWeight_ne_zero _),
      one_smul,hJF]
    rfl
  rw [h,Matrix.blockDiagonal'_one]

theorem natFourCOMBlockInverse_right (D : ℕ) (dim : Fin (D+1) → ℕ)
    (F J : ∀ d, Matrix (Fin (dim d)) (Fin (dim d)) ℂ)
    (hFJ : ∀ d, F d*J d=1) :
    natFourCOMBlockGram D dim F*natFourCOMBlockInverse D dim J=1 := by
  unfold natFourCOMBlockInverse natFourCOMBlockGram
  rw [←Matrix.blockDiagonal'_mul]
  have h : (fun d => (natFourCOMWeight (D-d.val) • F d) *
      ((natFourCOMWeight (D-d.val))⁻¹ • J d)) = (1 : ∀ d, Matrix (Fin (dim d)) (Fin (dim d)) ℂ) := by
    funext d
    rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,mul_inv_cancel₀ (natFourCOMWeight_ne_zero _),
      one_smul,hFJ]
    rfl
  rw [h,Matrix.blockDiagonal'_one]

theorem natFourCOMSigmaFamily_reindexed_gram {n : ℕ}
    (D : ℕ) (dim : Fin (D+1) → ℕ)
    (u : ∀ d, Fin (dim d) → Core ℕ ℂ)
    (F : ∀ d, Matrix (Fin (dim d)) (Fin (dim d)) ℂ)
    (hN : ∀ d a, (u d a).IsHomogeneous 4)
    (hL : ∀ d a, canonicalCOMLowerNat (u d a)=0)
    (hF : ∀ d, natFamilyGram (u d)=F d)
    (e : Fin n ≃ Σ d, Fin (dim d)) :
    natFamilyGram (fun i => natFourCOMSigmaFamily D dim u (e i))=
      (natFourCOMBlockGram D dim F).submatrix e e := by
  ext i j
  exact congrFun (congrFun (natFourCOMSigmaFamily_gram D dim u F hN hL hF) (e i)) (e j)

theorem natFourCOMBlockInverse_reindexed_left {n : ℕ}
    (D : ℕ) (dim : Fin (D+1) → ℕ)
    (F J : ∀ d, Matrix (Fin (dim d)) (Fin (dim d)) ℂ)
    (hJF : ∀ d, J d*F d=1) (e : Fin n ≃ Σ d, Fin (dim d)) :
    (natFourCOMBlockInverse D dim J).submatrix e e *
      (natFourCOMBlockGram D dim F).submatrix e e=1 := by
  rw [Matrix.submatrix_mul_equiv,natFourCOMBlockInverse_left D dim F J hJF,
    Matrix.submatrix_one_equiv]

#print axioms natFourCOMWeight_ne_zero
#print axioms natFourCOMSigmaFamily_gram
#print axioms natFourCOMBlockInverse_left
#print axioms natFourCOMBlockInverse_right
#print axioms natFourCOMSigmaFamily_reindexed_gram
#print axioms natFourCOMBlockInverse_reindexed_left
end TorusLean.BosonFiniteCertificate
