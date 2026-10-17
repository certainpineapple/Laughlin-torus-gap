/- M2b: an exact rational congruence-certificate checker.
   The certificate consists only of rational entries L and d. It contains
   no positivity proposition, inverse, or physical bridge assumption. -/
import GramSingularControls
set_option autoImplicit false

open Matrix
open scoped ComplexOrder

namespace TorusLean.M2

def rationalPSDCheck {n : ℕ} (A L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ) : Bool :=
  decide (A = L * Matrix.diagonal d * Lᵀ ∧ ∀ i, 0 ≤ d i)

theorem rationalPSDCheck_spec {n : ℕ} (A L : Matrix (Fin n) (Fin n) ℚ)
    (d : Fin n → ℚ) :
    rationalPSDCheck A L d = true ↔ A = L * Matrix.diagonal d * Lᵀ ∧ ∀ i, 0 ≤ d i := by
  simp [rationalPSDCheck]

noncomputable def complexify {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ) : Matrix (Fin m) (Fin n) ℂ :=
  A.map (Rat.castHom ℂ)

theorem complexify_congruence {n : ℕ} (L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ) :
    complexify (L * Matrix.diagonal d * Lᵀ) =
      complexify L * Matrix.diagonal (fun i => (d i : ℂ)) * (complexify L)ᴴ := by
  dsimp only [complexify]
  rw [Matrix.map_mul, Matrix.map_mul]
  have hd : (Matrix.diagonal d).map (Rat.castHom ℂ) =
      Matrix.diagonal (fun i => (d i : ℂ)) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  have ht : Lᵀ.map (Rat.castHom ℂ) = (L.map (Rat.castHom ℂ))ᴴ := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [hd, ht]

theorem rationalPSDCheck_sound {n : ℕ} (A L : Matrix (Fin n) (Fin n) ℚ)
    (d : Fin n → ℚ) (h : rationalPSDCheck A L d = true) :
    (complexify A).PosSemidef := by
  obtain ⟨heq, hd⟩ := (rationalPSDCheck_spec A L d).mp h
  have hdC : ∀ i, 0 ≤ (d i : ℂ) := by
    intro i
    have hr : 0 ≤ (d i : ℝ) := by exact_mod_cast hd i
    simpa using Complex.zero_le_real.mpr hr
  have hdiag := Matrix.PosSemidef.diagonal hdC
  have hcong := hdiag.mul_mul_conjTranspose_same (complexify L)
  rw [heq, complexify_congruence]
  exact hcong

theorem rationalPSDCheck_reject_nonPSD {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (h : ¬ (complexify A).PosSemidef) (L : Matrix (Fin n) (Fin n) ℚ)
    (d : Fin n → ℚ) : rationalPSDCheck A L d = false := by
  cases hc : rationalPSDCheck A L d with
  | false => rfl
  | true => exact (h (rationalPSDCheck_sound A L d hc)).elim

theorem psd_zero_diag_column {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) (i : n) (hi : A i i = 0) :
    ∀ j, A j i = 0 := by
  have hq : star (Pi.single i (1 : ℂ)) ⬝ᵥ A *ᵥ Pi.single i 1 = 0 := by
    simpa using hi
  have hz := hA.dotProduct_mulVec_zero_iff.mp hq
  intro j
  simpa using congrFun hz j

theorem psd_zero_diag_row {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.PosSemidef) (i : n) (hi : A i i = 0) :
    ∀ j, A i j = 0 := by
  intro j
  have hc := psd_zero_diag_column hA i hi j
  have he := congrFun (congrFun hA.isHermitian.eq i) j
  simpa [Matrix.conjTranspose_apply, hc] using he.symm

theorem zero_pivot_block_iff {n : Type*} [Fintype n] [DecidableEq n]
    (B : Matrix Unit n ℂ) (D : Matrix n n ℂ) :
    (Matrix.fromBlocks (0 : Matrix Unit Unit ℂ) B Bᴴ D).PosSemidef ↔
      B = 0 ∧ D.PosSemidef := by
  constructor
  · intro h
    constructor
    · ext i j
      cases i
      simpa using psd_zero_diag_row h (Sum.inl ()) (by simp) (Sum.inr j)
    · exact h.submatrix Sum.inr
  · rintro ⟨rfl, hD⟩
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · simp only [Matrix.isHermitian_fromBlocks_iff]
      exact ⟨Matrix.isHermitian_zero, by simp, by simp, hD.isHermitian⟩
    · intro x
      simpa [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Matrix.fromBlocks]
        using hD.dotProduct_mulVec_nonneg (x ∘ Sum.inr)

def rationalSingularDiagonal : Matrix (Fin 2) (Fin 2) ℚ :=
  Matrix.diagonal (fun i => if i = 0 then 1 else 0)

def rationalIndefiniteDiagonal : Matrix (Fin 2) (Fin 2) ℚ :=
  Matrix.diagonal (fun i => if i = 0 then 1 else -1)

def rationalBadZeroPivot : Matrix (Fin 2) (Fin 2) ℚ :=
  fun i j => if i = j then 0 else 1

def rationalFirstPivot : Fin 2 → ℚ := fun i => if i = 0 then 1 else 0

theorem rationalPSDCheck_singular_accept :
    rationalPSDCheck rationalSingularDiagonal 1 rationalFirstPivot = true := by decide +kernel

theorem rationalPSDCheck_rank_one_accept :
    rationalPSDCheck (fun _ _ : Fin 2 => 1)
      (fun _ j : Fin 2 => if j = 0 then 1 else 0) rationalFirstPivot = true := by decide +kernel

theorem rationalPSDCheck_negative_diagonal_reject :
    rationalPSDCheck rationalIndefiniteDiagonal 1
      (fun i : Fin 2 => if i = 0 then 1 else -1) = false := by decide +kernel

theorem rationalPSDCheck_bad_zero_pivot_reject :
    rationalPSDCheck rationalBadZeroPivot 1 (fun _ => 0) = false := by decide +kernel

theorem rationalPSDCheck_wrong_factor_reject :
    rationalPSDCheck (1 : Matrix (Fin 2) (Fin 2) ℚ) 1 (fun _ => 0) = false := by decide +kernel

theorem rationalPSDCheck_empty_accept :
    rationalPSDCheck (0 : Matrix (Fin 0) (Fin 0) ℚ) 0 (fun _ => 0) = true := by decide +kernel

#print axioms rationalPSDCheck_spec
#print axioms complexify_congruence
#print axioms rationalPSDCheck_sound
#print axioms rationalPSDCheck_reject_nonPSD
#print axioms psd_zero_diag_column
#print axioms psd_zero_diag_row
#print axioms zero_pivot_block_iff
#print axioms rationalPSDCheck_singular_accept
#print axioms rationalPSDCheck_rank_one_accept
#print axioms rationalPSDCheck_negative_diagonal_reject
#print axioms rationalPSDCheck_bad_zero_pivot_reject
#print axioms rationalPSDCheck_wrong_factor_reject
#print axioms rationalPSDCheck_empty_accept

end TorusLean.M2
