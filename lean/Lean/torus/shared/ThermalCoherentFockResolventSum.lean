import torus.shared.ThermalCoherentFockDirectSum
import torus.shared.ThermalCoherentFockResolventBlock

/-! The actual uniformly bounded inverse on the completed Hilbert sum.
Both inverse identities use the original unbounded operator and its exact
graph domain; membership is proved from Hx=lambda*x+y. The finite-sector
form hypothesis is explicit throughout. -/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.ThermalCoherentFockResolventSum
open TorusLean.Shared.ThermalCoherentFockDirectSum
open TorusLean.Shared.ThermalCoherentFockResolventBlock
open scoped ENNReal
variable {E : ℕ → Type*} [∀ n, NormedAddCommGroup (E n)]
  [∀ n, InnerProductSpace ℂ (E n)]

private theorem boundedCoordinates_mem (B : ∀ n, E n →L[ℂ] E n)
    (C : ℝ) (hC : 0 ≤ C) (hB : ∀ n v, ‖B n v‖ ≤ C*‖v‖) (x : lp E 2) :
    Memℓp (fun n => B n (x n)) 2 := by
  apply ((lp.memℓp x).const_smul (C : ℂ)).mono'
  intro n
  change ‖B n (x n)‖ ≤ ‖(C : ℂ) • x n‖
  simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC] using hB n (x n)

private def boundedCoordinates (B : ∀ n, E n →L[ℂ] E n)
    (C : ℝ) (hC : 0 ≤ C) (hB : ∀ n v, ‖B n v‖ ≤ C*‖v‖) : lp E 2 →ₗ[ℂ] lp E 2 where
  toFun x := ⟨fun n => B n (x n),boundedCoordinates_mem B C hC hB x⟩
  map_add' x y := by apply lp.ext; funext n; exact map_add (B n) _ _
  map_smul' c x := by apply lp.ext; funext n; exact map_smul (B n) c _

private theorem boundedCoordinates_norm (B : ∀ n, E n →L[ℂ] E n)
    (C : ℝ) (hC : 0 ≤ C) (hB : ∀ n v, ‖B n v‖ ≤ C*‖v‖) (x : lp E 2) :
    ‖boundedCoordinates B C hC hB x‖ ≤ C*‖x‖ := by
  calc
    ‖boundedCoordinates B C hC hB x‖ ≤ ‖(C : ℂ) • x‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro n
      change ‖B n (x n)‖ ≤ ‖(C : ℂ) • x n‖
      simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC] using hB n (x n)
    _ = C*‖x‖ := by rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC]

/-- A bounded diagonal map on the genuine lp completion. -/
def boundedDirectSum (B : ∀ n, E n →L[ℂ] E n)
    (C : ℝ) (hC : 0 ≤ C) (hB : ∀ n v, ‖B n v‖ ≤ C*‖v‖) : lp E 2 →L[ℂ] lp E 2 :=
  (boundedCoordinates B C hC hB).mkContinuous C (boundedCoordinates_norm B C hC hB)

theorem boundedDirectSum_apply (B : ∀ n, E n →L[ℂ] E n)
    (C : ℝ) (hC : 0 ≤ C) (hB : ∀ n v, ‖B n v‖ ≤ C*‖v‖) (x : lp E 2) (n : ℕ) :
    boundedDirectSum B C hC hB x n = B n (x n) := rfl

theorem boundedDirectSum_norm_le (B : ∀ n, E n →L[ℂ] E n)
    (C : ℝ) (hC : 0 ≤ C) (hB : ∀ n v, ‖B n v‖ ≤ C*‖v‖) :
    ‖boundedDirectSum B C hC hB‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC _

variable [∀ n, FiniteDimensional ℂ (E n)]

/-- Genuine global bounded inverse candidate assembled from the proven
finite-sector inverses with one common bound. -/
def directSumResolvent (H : ∀ n, E n →L[ℂ] E n) (gamma lambda : ℝ)
    (hlambda : 0 < lambda) (hlambda' : lambda < gamma)
    (hform : ∀ n x, gamma*(inner ℂ x (H n x)).re ≤ ‖H n x‖^2) :
    lp E 2 →L[ℂ] lp E 2 :=
  boundedDirectSum (fun n => blockResolvent (H n) gamma lambda hlambda hlambda' (hform n))
    (min lambda (gamma-lambda))⁻¹
    (inv_nonneg.mpr (le_of_lt (lt_min hlambda (sub_pos.mpr hlambda'))))
    (fun n => blockResolvent_norm_le (H n) gamma lambda hlambda hlambda' (hform n))

theorem directSumResolvent_apply (H : ∀ n, E n →L[ℂ] E n) (gamma lambda : ℝ)
    (hlambda : 0 < lambda) (hlambda' : lambda < gamma)
    (hform : ∀ n x, gamma*(inner ℂ x (H n x)).re ≤ ‖H n x‖^2)
    (y : lp E 2) (n : ℕ) :
    directSumResolvent H gamma lambda hlambda hlambda' hform y n =
      blockResolvent (H n) gamma lambda hlambda hlambda' (hform n) (y n) := rfl

theorem directSumResolvent_norm_le (H : ∀ n, E n →L[ℂ] E n) (gamma lambda : ℝ)
    (hlambda : 0 < lambda) (hlambda' : lambda < gamma)
    (hform : ∀ n x, gamma*(inner ℂ x (H n x)).re ≤ ‖H n x‖^2) :
    ‖directSumResolvent H gamma lambda hlambda hlambda' hform‖ ≤
      (min lambda (gamma-lambda))⁻¹ :=
  boundedDirectSum_norm_le _ _ _ _

/-- The inverse output really lies in D(H): its block-H image equals lambda*x+y,
which is a genuine lp vector. No formal totalization outside the domain is used. -/
theorem directSumResolvent_mem_domain (H : ∀ n, E n →L[ℂ] E n) (gamma lambda : ℝ)
    (hlambda : 0 < lambda) (hlambda' : lambda < gamma)
    (hform : ∀ n x, gamma*(inner ℂ x (H n x)).re ≤ ‖H n x‖^2) (y : lp E 2) :
    directSumResolvent H gamma lambda hlambda hlambda' hform y ∈ (blockDirectSum H).domain := by
  let x := directSumResolvent H gamma lambda hlambda hlambda' hform y
  change Memℓp (fun n => H n (x n)) 2
  have he : (fun n => H n (x n)) = ((lambda : ℂ) • x + y : lp E 2) := by
    funext n
    change H n (blockResolvent (H n) gamma lambda hlambda hlambda' (hform n) (y n)) =
      (lambda : ℂ) • blockResolvent (H n) gamma lambda hlambda hlambda' (hform n) (y n)+y n
    have h := blockResolvent_right_inverse (H n) gamma lambda hlambda hlambda' (hform n) (y n)
    rw [shiftedBlock_apply] at h
    exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)
  rw [he]
  exact lp.memℓp _

theorem directSumResolvent_right_inverse (H : ∀ n, E n →L[ℂ] E n) (gamma lambda : ℝ)
    (hlambda : 0 < lambda) (hlambda' : lambda < gamma)
    (hform : ∀ n x, gamma*(inner ℂ x (H n x)).re ≤ ‖H n x‖^2) (y : lp E 2) :
    blockDirectSum H ⟨directSumResolvent H gamma lambda hlambda hlambda' hform y,
      directSumResolvent_mem_domain H gamma lambda hlambda hlambda' hform y⟩ -
      (lambda : ℂ) • directSumResolvent H gamma lambda hlambda hlambda' hform y = y := by
  apply lp.ext
  funext n
  exact blockResolvent_right_inverse (H n) gamma lambda hlambda hlambda' (hform n) (y n)

theorem directSumResolvent_left_inverse (H : ∀ n, E n →L[ℂ] E n) (gamma lambda : ℝ)
    (hlambda : 0 < lambda) (hlambda' : lambda < gamma)
    (hform : ∀ n x, gamma*(inner ℂ x (H n x)).re ≤ ‖H n x‖^2)
    (x : (blockDirectSum H).domain) :
    directSumResolvent H gamma lambda hlambda hlambda' hform
      (blockDirectSum H x - (lambda : ℂ) • x.val) = x.val := by
  apply lp.ext
  funext n
  exact blockResolvent_left_inverse (H n) gamma lambda hlambda hlambda' (hform n) (x.val n)

end TorusLean.Shared.ThermalCoherentFockResolventSum
