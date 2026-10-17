import torus.shared.BosonFiniteCertificateCanonicalCOMRaise

/-! Genuine finite COM lowering and vacuum descendants, in the same factorial
coordinates as actual raising. These statements concern the complete
three-particle degree blocks 0,...,8. No boundary CCR is asserted on arbitrary
polynomials in nine variables. R and L are the unnormalized total generators. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix
open scoped BigOperators
open TorusLean.M2
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.BosonFiniteCertificateCoordinate

/-- Actual paper-coordinate lowering, including the orbital index coefficient. -/
def finitePaperLower9 : Core (Fin 9) ℂ →ₗ[ℂ] Core (Fin 9) ℂ :=
  ∑ j : Fin 8, (j.val + 1 : ℂ) • normalWord [raiseSource9 j] [raiseTarget9 j]

def canonicalCOMLower9 : Core (Fin 9) ℂ →ₗ[ℂ] Core (Fin 9) ℂ :=
  conjugateOperator factorialRoot9 factorialRoot9_ne_zero finitePaperLower9

theorem finitePaperLower9_word (s : List (Fin 9)) :
    finitePaperLower9 (wordPolynomial s) =
      ∑ j : Fin 8, ((j.val + 1 : ℂ) * (s.count (raiseTarget9 j) : ℂ)) •
        wordPolynomial (raiseSource9 j :: s.erase (raiseTarget9 j)) := by
  simp [finitePaperLower9, LinearMap.sum_apply, normalWord_wordPolynomial,
    wordRemovalWeight, eraseWord, smul_smul]

theorem canonicalCOMLower9_scaledWord (s : List (Fin 9)) :
    canonicalCOMLower9 (scaledWord factorialRoot9 s) =
      ∑ j : Fin 8, ((j.val + 1 : ℂ) * (s.count (raiseTarget9 j) : ℂ)) •
        scaledWord factorialRoot9 (raiseSource9 j :: s.erase (raiseTarget9 j)) := by
  rw [canonicalCOMLower9, ← rescaleEquiv_word factorialRoot9 factorialRoot9_ne_zero,
    conjugateOperator_apply_rescale, finitePaperLower9_word, map_sum]
  simp only [map_smul, rescaleEquiv_word]

theorem complexify_zero_rect {m n : ℕ} :
    complexify (0 : Matrix (Fin m) (Fin n) ℚ) = 0 := by
  ext i j; simp [complexify]

theorem lower_complexify_add_rect {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ) :
    complexify (A + B) = complexify A + complexify B := by
  ext i j; simp [complexify]

theorem lower_complexify_smul_rat {m n : ℕ} (q : ℚ) (M : Matrix (Fin m) (Fin n) ℚ) :
    complexify (q • M) = (q : ℂ) • complexify M := by
  ext i j; simp [complexify]

theorem canonicalBlock_zero9 {n : ℕ} (occ : Fin n → (Fin 9 →₀ ℕ)) :
    canonicalBlock (factorialScale 8) occ (0 : Fin n → ℂ) = 0 := by
  simp [canonicalBlock]

theorem canonicalBlock_add9 {n : ℕ} (occ : Fin n → (Fin 9 →₀ ℕ))
    (x y : Fin n → ℂ) :
    canonicalBlock (factorialScale 8) occ (x+y) =
      canonicalBlock (factorialScale 8) occ x + canonicalBlock (factorialScale 8) occ y := by
  simp [canonicalBlock, add_smul, Finset.sum_add_distrib]

theorem canonicalBlock_smul9 {n : ℕ} (occ : Fin n → (Fin 9 →₀ ℕ))
    (q : ℂ) (x : Fin n → ℂ) :
    canonicalBlock (factorialScale 8) occ (q • x) =
      q • canonicalBlock (factorialScale 8) occ x := by
  simp [canonicalBlock, Finset.smul_sum, smul_smul]

theorem k300_paper_lower_word (a : Fin 1) :
    finitePaperLower9 (wordPolynomial ((p300basis a).map fin9)) = 0 := by
  rw [finitePaperLower9_word]
  fin_cases a
  norm_num [Fin.sum_univ_succ, p300basis, raiseSource9, raiseTarget9, fin9]

theorem k300_actual_canonical_lower (a : Fin 1) :
    canonicalCOMLower9 (canonicalMonomial (factorialScale 8) (k300occ a)) = 0 := by
  rw [canonicalCOMLower9, ← k300_canonical_source_word,
    ← rescaleEquiv_word factorialRoot9 factorialRoot9_ne_zero,
    conjugateOperator_apply_rescale, k300_paper_lower_word, map_zero]

theorem k300_actual_lower_block (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k300occ x) = 0 := by
  simp [canonicalBlock, map_sum, map_smul, k300_actual_canonical_lower]

theorem k301_paper_lower_word (a : Fin 1) :
    finitePaperLower9 (wordPolynomial ((p301basis a).map fin9)) =
      ∑ i : Fin 1, (b301lower i a : ℂ) •
        wordPolynomial ((p300basis i).map fin9) := by
  fin_cases a <;>
    simp only [finitePaperLower9, LinearMap.sum_apply, LinearMap.smul_apply,
      normalWord_wordPolynomial] <;>
    norm_num [Fin.sum_univ_succ, p301basis, p300basis, b301lower,
      wordRemovalWeight, eraseWord, wordPolynomial, raiseSource9, raiseTarget9,
      fin9, Algebra.smul_def] <;> (try simp only [map_ofNat]) <;> ring

theorem k301_actual_canonical_lower (a : Fin 1) :
    canonicalCOMLower9 (canonicalMonomial (factorialScale 8) (k301occ a)) =
      ∑ i : Fin 1, (b301lower i a : ℂ) •
        canonicalMonomial (factorialScale 8) (k300occ i) := by
  rw [canonicalCOMLower9, ← k301_canonical_source_word,
    ← rescaleEquiv_word factorialRoot9 factorialRoot9_ne_zero,
    conjugateOperator_apply_rescale, k301_paper_lower_word, map_sum]
  simp only [map_smul, rescaleEquiv_word, k300_canonical_source_word]

theorem k301_actual_lower_block (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k301occ x) =
      canonicalBlock (factorialScale 8) k300occ (complexify b301lower *ᵥ x) := by
  exact canonicalBlock_rect_action k301occ k300occ canonicalCOMLower9
    (complexify b301lower) k301_actual_canonical_lower x

theorem k302_paper_lower_word (a : Fin 2) :
    finitePaperLower9 (wordPolynomial ((p302basis a).map fin9)) =
      ∑ i : Fin 1, (b302lower i a : ℂ) •
        wordPolynomial ((p301basis i).map fin9) := by
  fin_cases a <;>
    simp only [finitePaperLower9, LinearMap.sum_apply, LinearMap.smul_apply,
      normalWord_wordPolynomial] <;>
    norm_num [Fin.sum_univ_succ, p302basis, p301basis, b302lower,
      wordRemovalWeight, eraseWord, wordPolynomial, raiseSource9, raiseTarget9,
      fin9, Algebra.smul_def] <;> (try simp only [map_ofNat]) <;> ring

theorem k302_actual_canonical_lower (a : Fin 2) :
    canonicalCOMLower9 (canonicalMonomial (factorialScale 8) (k302occ a)) =
      ∑ i : Fin 1, (b302lower i a : ℂ) •
        canonicalMonomial (factorialScale 8) (k301occ i) := by
  rw [canonicalCOMLower9, ← k302_canonical_source_word,
    ← rescaleEquiv_word factorialRoot9 factorialRoot9_ne_zero,
    conjugateOperator_apply_rescale, k302_paper_lower_word, map_sum]
  simp only [map_smul, rescaleEquiv_word, k301_canonical_source_word]

theorem k302_actual_lower_block (x : Fin 2 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k302occ x) =
      canonicalBlock (factorialScale 8) k301occ (complexify b302lower *ᵥ x) := by
  exact canonicalBlock_rect_action k302occ k301occ canonicalCOMLower9
    (complexify b302lower) k302_actual_canonical_lower x

theorem k303_paper_lower_word (a : Fin 3) :
    finitePaperLower9 (wordPolynomial ((p303basis a).map fin9)) =
      ∑ i : Fin 2, (b303lower i a : ℂ) •
        wordPolynomial ((p302basis i).map fin9) := by
  fin_cases a <;>
    simp only [finitePaperLower9, LinearMap.sum_apply, LinearMap.smul_apply,
      normalWord_wordPolynomial] <;>
    norm_num [Fin.sum_univ_succ, p303basis, p302basis, b303lower,
      wordRemovalWeight, eraseWord, wordPolynomial, raiseSource9, raiseTarget9,
      fin9, Algebra.smul_def] <;> (try simp only [map_ofNat]) <;> ring

theorem k303_actual_canonical_lower (a : Fin 3) :
    canonicalCOMLower9 (canonicalMonomial (factorialScale 8) (k303occ a)) =
      ∑ i : Fin 2, (b303lower i a : ℂ) •
        canonicalMonomial (factorialScale 8) (k302occ i) := by
  rw [canonicalCOMLower9, ← k303_canonical_source_word,
    ← rescaleEquiv_word factorialRoot9 factorialRoot9_ne_zero,
    conjugateOperator_apply_rescale, k303_paper_lower_word, map_sum]
  simp only [map_smul, rescaleEquiv_word, k302_canonical_source_word]

theorem k303_actual_lower_block (x : Fin 3 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k303occ x) =
      canonicalBlock (factorialScale 8) k302occ (complexify b303lower *ᵥ x) := by
  exact canonicalBlock_rect_action k303occ k302occ canonicalCOMLower9
    (complexify b303lower) k303_actual_canonical_lower x

theorem k304_paper_lower_word (a : Fin 4) :
    finitePaperLower9 (wordPolynomial ((p304basis a).map fin9)) =
      ∑ i : Fin 3, (b304lower i a : ℂ) •
        wordPolynomial ((p303basis i).map fin9) := by
  fin_cases a <;>
    simp only [finitePaperLower9, LinearMap.sum_apply, LinearMap.smul_apply,
      normalWord_wordPolynomial] <;>
    norm_num [Fin.sum_univ_succ, p304basis, p303basis, b304lower,
      wordRemovalWeight, eraseWord, wordPolynomial, raiseSource9, raiseTarget9,
      fin9, Algebra.smul_def] <;> (try simp only [map_ofNat]) <;> ring

theorem k304_actual_canonical_lower (a : Fin 4) :
    canonicalCOMLower9 (canonicalMonomial (factorialScale 8) (k304occ a)) =
      ∑ i : Fin 3, (b304lower i a : ℂ) •
        canonicalMonomial (factorialScale 8) (k303occ i) := by
  rw [canonicalCOMLower9, ← k304_canonical_source_word,
    ← rescaleEquiv_word factorialRoot9 factorialRoot9_ne_zero,
    conjugateOperator_apply_rescale, k304_paper_lower_word, map_sum]
  simp only [map_smul, rescaleEquiv_word, k303_canonical_source_word]

theorem k304_actual_lower_block (x : Fin 4 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k304occ x) =
      canonicalBlock (factorialScale 8) k303occ (complexify b304lower *ᵥ x) := by
  exact canonicalBlock_rect_action k304occ k303occ canonicalCOMLower9
    (complexify b304lower) k304_actual_canonical_lower x

theorem k305_paper_lower_word (a : Fin 5) :
    finitePaperLower9 (wordPolynomial ((p305basis a).map fin9)) =
      ∑ i : Fin 4, (b305lower i a : ℂ) •
        wordPolynomial ((p304basis i).map fin9) := by
  fin_cases a <;>
    simp only [finitePaperLower9, LinearMap.sum_apply, LinearMap.smul_apply,
      normalWord_wordPolynomial] <;>
    norm_num [Fin.sum_univ_succ, p305basis, p304basis, b305lower,
      wordRemovalWeight, eraseWord, wordPolynomial, raiseSource9, raiseTarget9,
      fin9, Algebra.smul_def] <;> (try simp only [map_ofNat]) <;> ring

theorem k305_actual_canonical_lower (a : Fin 5) :
    canonicalCOMLower9 (canonicalMonomial (factorialScale 8) (k305occ a)) =
      ∑ i : Fin 4, (b305lower i a : ℂ) •
        canonicalMonomial (factorialScale 8) (k304occ i) := by
  rw [canonicalCOMLower9, ← k305_canonical_source_word,
    ← rescaleEquiv_word factorialRoot9 factorialRoot9_ne_zero,
    conjugateOperator_apply_rescale, k305_paper_lower_word, map_sum]
  simp only [map_smul, rescaleEquiv_word, k304_canonical_source_word]

theorem k305_actual_lower_block (x : Fin 5 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k305occ x) =
      canonicalBlock (factorialScale 8) k304occ (complexify b305lower *ᵥ x) := by
  exact canonicalBlock_rect_action k305occ k304occ canonicalCOMLower9
    (complexify b305lower) k305_actual_canonical_lower x

theorem k306_paper_lower_word (a : Fin 7) :
    finitePaperLower9 (wordPolynomial ((p306basis a).map fin9)) =
      ∑ i : Fin 5, (b306lower i a : ℂ) •
        wordPolynomial ((p305basis i).map fin9) := by
  fin_cases a <;>
    simp only [finitePaperLower9, LinearMap.sum_apply, LinearMap.smul_apply,
      normalWord_wordPolynomial] <;>
    norm_num [Fin.sum_univ_succ, p306basis, p305basis, b306lower,
      wordRemovalWeight, eraseWord, wordPolynomial, raiseSource9, raiseTarget9,
      fin9, Algebra.smul_def] <;> (try simp only [map_ofNat]) <;> ring

theorem k306_actual_canonical_lower (a : Fin 7) :
    canonicalCOMLower9 (canonicalMonomial (factorialScale 8) (k306occ a)) =
      ∑ i : Fin 5, (b306lower i a : ℂ) •
        canonicalMonomial (factorialScale 8) (k305occ i) := by
  rw [canonicalCOMLower9, ← k306_canonical_source_word,
    ← rescaleEquiv_word factorialRoot9 factorialRoot9_ne_zero,
    conjugateOperator_apply_rescale, k306_paper_lower_word, map_sum]
  simp only [map_smul, rescaleEquiv_word, k305_canonical_source_word]

theorem k306_actual_lower_block (x : Fin 7 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k306occ x) =
      canonicalBlock (factorialScale 8) k305occ (complexify b306lower *ᵥ x) := by
  exact canonicalBlock_rect_action k306occ k305occ canonicalCOMLower9
    (complexify b306lower) k306_actual_canonical_lower x

theorem k307_paper_lower_word (a : Fin 8) :
    finitePaperLower9 (wordPolynomial ((p307basis a).map fin9)) =
      ∑ i : Fin 7, (b307lower i a : ℂ) •
        wordPolynomial ((p306basis i).map fin9) := by
  fin_cases a <;>
    simp only [finitePaperLower9, LinearMap.sum_apply, LinearMap.smul_apply,
      normalWord_wordPolynomial] <;>
    norm_num [Fin.sum_univ_succ, p307basis, p306basis, b307lower,
      wordRemovalWeight, eraseWord, wordPolynomial, raiseSource9, raiseTarget9,
      fin9, Algebra.smul_def] <;> (try simp only [map_ofNat]) <;> ring

theorem k307_actual_canonical_lower (a : Fin 8) :
    canonicalCOMLower9 (canonicalMonomial (factorialScale 8) (k307occ a)) =
      ∑ i : Fin 7, (b307lower i a : ℂ) •
        canonicalMonomial (factorialScale 8) (k306occ i) := by
  rw [canonicalCOMLower9, ← k307_canonical_source_word,
    ← rescaleEquiv_word factorialRoot9 factorialRoot9_ne_zero,
    conjugateOperator_apply_rescale, k307_paper_lower_word, map_sum]
  simp only [map_smul, rescaleEquiv_word, k306_canonical_source_word]

theorem k307_actual_lower_block (x : Fin 8 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k307occ x) =
      canonicalBlock (factorialScale 8) k306occ (complexify b307lower *ᵥ x) := by
  exact canonicalBlock_rect_action k307occ k306occ canonicalCOMLower9
    (complexify b307lower) k307_actual_canonical_lower x

theorem k308_paper_lower_word (a : Fin 10) :
    finitePaperLower9 (wordPolynomial ((p308basis a).map fin9)) =
      ∑ i : Fin 8, (b308lower i a : ℂ) •
        wordPolynomial ((p307basis i).map fin9) := by
  fin_cases a <;>
    simp only [finitePaperLower9, LinearMap.sum_apply, LinearMap.smul_apply,
      normalWord_wordPolynomial] <;>
    norm_num [Fin.sum_univ_succ, p308basis, p307basis, b308lower,
      wordRemovalWeight, eraseWord, wordPolynomial, raiseSource9, raiseTarget9,
      fin9, Algebra.smul_def] <;> (try simp only [map_ofNat]) <;> ring

theorem k308_actual_canonical_lower (a : Fin 10) :
    canonicalCOMLower9 (canonicalMonomial (factorialScale 8) (k308occ a)) =
      ∑ i : Fin 8, (b308lower i a : ℂ) •
        canonicalMonomial (factorialScale 8) (k307occ i) := by
  rw [canonicalCOMLower9, ← k308_canonical_source_word,
    ← rescaleEquiv_word factorialRoot9 factorialRoot9_ne_zero,
    conjugateOperator_apply_rescale, k308_paper_lower_word, map_sum]
  simp only [map_smul, rescaleEquiv_word, k307_canonical_source_word]

theorem k308_actual_lower_block (x : Fin 10 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k308occ x) =
      canonicalBlock (factorialScale 8) k307occ (complexify b308lower *ᵥ x) := by
  exact canonicalBlock_rect_action k308occ k307occ canonicalCOMLower9
    (complexify b308lower) k308_actual_canonical_lower x

theorem k300_actual_relative_vacuum (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k300occ
      (complexify b300relative *ᵥ x)) = 0 := by
  exact k300_actual_lower_block _

theorem k301_actual_relative_vacuum (x : Fin 0 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k301occ
      (complexify b301relative *ᵥ x)) = 0 := by
  rw [k301_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    b301_relative_annihilated, complexify_zero_rect, Matrix.zero_mulVec,
    canonicalBlock_zero9]

theorem k302_actual_relative_vacuum (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k302occ
      (complexify b302relative *ᵥ x)) = 0 := by
  rw [k302_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    b302_relative_annihilated, complexify_zero_rect, Matrix.zero_mulVec,
    canonicalBlock_zero9]

theorem k303_actual_relative_vacuum (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k303occ
      (complexify b303relative *ᵥ x)) = 0 := by
  rw [k303_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    b303_relative_annihilated, complexify_zero_rect, Matrix.zero_mulVec,
    canonicalBlock_zero9]

theorem k304_actual_relative_vacuum (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k304occ
      (complexify b304relative *ᵥ x)) = 0 := by
  rw [k304_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    b304_relative_annihilated, complexify_zero_rect, Matrix.zero_mulVec,
    canonicalBlock_zero9]

theorem k305_actual_relative_vacuum (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k305occ
      (complexify b305relative *ᵥ x)) = 0 := by
  rw [k305_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    b305_relative_annihilated, complexify_zero_rect, Matrix.zero_mulVec,
    canonicalBlock_zero9]

theorem k306_actual_relative_vacuum (x : Fin 2 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k306occ
      (complexify b306relative *ᵥ x)) = 0 := by
  rw [k306_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    b306_relative_annihilated, complexify_zero_rect, Matrix.zero_mulVec,
    canonicalBlock_zero9]

theorem k307_actual_relative_vacuum (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k307occ
      (complexify b307relative *ᵥ x)) = 0 := by
  rw [k307_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    b307_relative_annihilated, complexify_zero_rect, Matrix.zero_mulVec,
    canonicalBlock_zero9]

theorem k308_actual_relative_vacuum (x : Fin 2 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k308occ
      (complexify b308relative *ᵥ x)) = 0 := by
  rw [k308_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    b308_relative_annihilated, complexify_zero_rect, Matrix.zero_mulVec,
    canonicalBlock_zero9]

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c300desc1_lower_matrix :
    b301lower * c300desc1 = (3 : ℚ) • c300desc0 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c300desc1_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k301occ
      (complexify c300desc1 *ᵥ x)) =
      (3 : ℂ) • canonicalBlock (factorialScale 8) k300occ
        (complexify c300desc0 *ᵥ x) := by
  rw [k301_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c300desc1_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c300desc2_lower_matrix :
    b302lower * c300desc2 = (6 : ℚ) • c300desc1 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c300desc2_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k302occ
      (complexify c300desc2 *ᵥ x)) =
      (6 : ℂ) • canonicalBlock (factorialScale 8) k301occ
        (complexify c300desc1 *ᵥ x) := by
  rw [k302_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c300desc2_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c300desc3_lower_matrix :
    b303lower * c300desc3 = (9 : ℚ) • c300desc2 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c300desc3_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k303occ
      (complexify c300desc3 *ᵥ x)) =
      (9 : ℂ) • canonicalBlock (factorialScale 8) k302occ
        (complexify c300desc2 *ᵥ x) := by
  rw [k303_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c300desc3_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c300desc4_lower_matrix :
    b304lower * c300desc4 = (12 : ℚ) • c300desc3 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c300desc4_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k304occ
      (complexify c300desc4 *ᵥ x)) =
      (12 : ℂ) • canonicalBlock (factorialScale 8) k303occ
        (complexify c300desc3 *ᵥ x) := by
  rw [k304_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c300desc4_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c300desc5_lower_matrix :
    b305lower * c300desc5 = (15 : ℚ) • c300desc4 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c300desc5_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k305occ
      (complexify c300desc5 *ᵥ x)) =
      (15 : ℂ) • canonicalBlock (factorialScale 8) k304occ
        (complexify c300desc4 *ᵥ x) := by
  rw [k305_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c300desc5_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c300desc6_lower_matrix :
    b306lower * c300desc6 = (18 : ℚ) • c300desc5 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c300desc6_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k306occ
      (complexify c300desc6 *ᵥ x)) =
      (18 : ℂ) • canonicalBlock (factorialScale 8) k305occ
        (complexify c300desc5 *ᵥ x) := by
  rw [k306_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c300desc6_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c300desc7_lower_matrix :
    b307lower * c300desc7 = (21 : ℚ) • c300desc6 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c300desc7_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k307occ
      (complexify c300desc7 *ᵥ x)) =
      (21 : ℂ) • canonicalBlock (factorialScale 8) k306occ
        (complexify c300desc6 *ᵥ x) := by
  rw [k307_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c300desc7_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c300desc8_lower_matrix :
    b308lower * c300desc8 = (24 : ℚ) • c300desc7 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c300desc8_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k308occ
      (complexify c300desc8 *ᵥ x)) =
      (24 : ℂ) • canonicalBlock (factorialScale 8) k307occ
        (complexify c300desc7 *ᵥ x) := by
  rw [k308_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c300desc8_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c301desc2_lower_matrix :
    b302lower * c301desc2 = (3 : ℚ) • c301desc1 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c301desc2_actual_lower (x : Fin 0 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k302occ
      (complexify c301desc2 *ᵥ x)) =
      (3 : ℂ) • canonicalBlock (factorialScale 8) k301occ
        (complexify c301desc1 *ᵥ x) := by
  rw [k302_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c301desc2_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c301desc3_lower_matrix :
    b303lower * c301desc3 = (6 : ℚ) • c301desc2 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c301desc3_actual_lower (x : Fin 0 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k303occ
      (complexify c301desc3 *ᵥ x)) =
      (6 : ℂ) • canonicalBlock (factorialScale 8) k302occ
        (complexify c301desc2 *ᵥ x) := by
  rw [k303_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c301desc3_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c301desc4_lower_matrix :
    b304lower * c301desc4 = (9 : ℚ) • c301desc3 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c301desc4_actual_lower (x : Fin 0 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k304occ
      (complexify c301desc4 *ᵥ x)) =
      (9 : ℂ) • canonicalBlock (factorialScale 8) k303occ
        (complexify c301desc3 *ᵥ x) := by
  rw [k304_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c301desc4_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c301desc5_lower_matrix :
    b305lower * c301desc5 = (12 : ℚ) • c301desc4 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c301desc5_actual_lower (x : Fin 0 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k305occ
      (complexify c301desc5 *ᵥ x)) =
      (12 : ℂ) • canonicalBlock (factorialScale 8) k304occ
        (complexify c301desc4 *ᵥ x) := by
  rw [k305_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c301desc5_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c301desc6_lower_matrix :
    b306lower * c301desc6 = (15 : ℚ) • c301desc5 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c301desc6_actual_lower (x : Fin 0 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k306occ
      (complexify c301desc6 *ᵥ x)) =
      (15 : ℂ) • canonicalBlock (factorialScale 8) k305occ
        (complexify c301desc5 *ᵥ x) := by
  rw [k306_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c301desc6_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c301desc7_lower_matrix :
    b307lower * c301desc7 = (18 : ℚ) • c301desc6 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c301desc7_actual_lower (x : Fin 0 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k307occ
      (complexify c301desc7 *ᵥ x)) =
      (18 : ℂ) • canonicalBlock (factorialScale 8) k306occ
        (complexify c301desc6 *ᵥ x) := by
  rw [k307_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c301desc7_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c301desc8_lower_matrix :
    b308lower * c301desc8 = (21 : ℚ) • c301desc7 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c301desc8_actual_lower (x : Fin 0 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k308occ
      (complexify c301desc8 *ᵥ x)) =
      (21 : ℂ) • canonicalBlock (factorialScale 8) k307occ
        (complexify c301desc7 *ᵥ x) := by
  rw [k308_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c301desc8_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c302desc3_lower_matrix :
    b303lower * c302desc3 = (3 : ℚ) • c302desc2 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c302desc3_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k303occ
      (complexify c302desc3 *ᵥ x)) =
      (3 : ℂ) • canonicalBlock (factorialScale 8) k302occ
        (complexify c302desc2 *ᵥ x) := by
  rw [k303_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c302desc3_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c302desc4_lower_matrix :
    b304lower * c302desc4 = (6 : ℚ) • c302desc3 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c302desc4_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k304occ
      (complexify c302desc4 *ᵥ x)) =
      (6 : ℂ) • canonicalBlock (factorialScale 8) k303occ
        (complexify c302desc3 *ᵥ x) := by
  rw [k304_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c302desc4_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c302desc5_lower_matrix :
    b305lower * c302desc5 = (9 : ℚ) • c302desc4 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c302desc5_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k305occ
      (complexify c302desc5 *ᵥ x)) =
      (9 : ℂ) • canonicalBlock (factorialScale 8) k304occ
        (complexify c302desc4 *ᵥ x) := by
  rw [k305_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c302desc5_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c302desc6_lower_matrix :
    b306lower * c302desc6 = (12 : ℚ) • c302desc5 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c302desc6_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k306occ
      (complexify c302desc6 *ᵥ x)) =
      (12 : ℂ) • canonicalBlock (factorialScale 8) k305occ
        (complexify c302desc5 *ᵥ x) := by
  rw [k306_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c302desc6_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c302desc7_lower_matrix :
    b307lower * c302desc7 = (15 : ℚ) • c302desc6 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c302desc7_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k307occ
      (complexify c302desc7 *ᵥ x)) =
      (15 : ℂ) • canonicalBlock (factorialScale 8) k306occ
        (complexify c302desc6 *ᵥ x) := by
  rw [k307_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c302desc7_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c302desc8_lower_matrix :
    b308lower * c302desc8 = (18 : ℚ) • c302desc7 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c302desc8_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k308occ
      (complexify c302desc8 *ᵥ x)) =
      (18 : ℂ) • canonicalBlock (factorialScale 8) k307occ
        (complexify c302desc7 *ᵥ x) := by
  rw [k308_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c302desc8_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c303desc4_lower_matrix :
    b304lower * c303desc4 = (3 : ℚ) • c303desc3 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c303desc4_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k304occ
      (complexify c303desc4 *ᵥ x)) =
      (3 : ℂ) • canonicalBlock (factorialScale 8) k303occ
        (complexify c303desc3 *ᵥ x) := by
  rw [k304_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c303desc4_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c303desc5_lower_matrix :
    b305lower * c303desc5 = (6 : ℚ) • c303desc4 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c303desc5_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k305occ
      (complexify c303desc5 *ᵥ x)) =
      (6 : ℂ) • canonicalBlock (factorialScale 8) k304occ
        (complexify c303desc4 *ᵥ x) := by
  rw [k305_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c303desc5_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c303desc6_lower_matrix :
    b306lower * c303desc6 = (9 : ℚ) • c303desc5 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c303desc6_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k306occ
      (complexify c303desc6 *ᵥ x)) =
      (9 : ℂ) • canonicalBlock (factorialScale 8) k305occ
        (complexify c303desc5 *ᵥ x) := by
  rw [k306_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c303desc6_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c303desc7_lower_matrix :
    b307lower * c303desc7 = (12 : ℚ) • c303desc6 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c303desc7_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k307occ
      (complexify c303desc7 *ᵥ x)) =
      (12 : ℂ) • canonicalBlock (factorialScale 8) k306occ
        (complexify c303desc6 *ᵥ x) := by
  rw [k307_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c303desc7_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c303desc8_lower_matrix :
    b308lower * c303desc8 = (15 : ℚ) • c303desc7 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c303desc8_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k308occ
      (complexify c303desc8 *ᵥ x)) =
      (15 : ℂ) • canonicalBlock (factorialScale 8) k307occ
        (complexify c303desc7 *ᵥ x) := by
  rw [k308_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c303desc8_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c304desc5_lower_matrix :
    b305lower * c304desc5 = (3 : ℚ) • c304desc4 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c304desc5_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k305occ
      (complexify c304desc5 *ᵥ x)) =
      (3 : ℂ) • canonicalBlock (factorialScale 8) k304occ
        (complexify c304desc4 *ᵥ x) := by
  rw [k305_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c304desc5_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c304desc6_lower_matrix :
    b306lower * c304desc6 = (6 : ℚ) • c304desc5 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c304desc6_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k306occ
      (complexify c304desc6 *ᵥ x)) =
      (6 : ℂ) • canonicalBlock (factorialScale 8) k305occ
        (complexify c304desc5 *ᵥ x) := by
  rw [k306_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c304desc6_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c304desc7_lower_matrix :
    b307lower * c304desc7 = (9 : ℚ) • c304desc6 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c304desc7_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k307occ
      (complexify c304desc7 *ᵥ x)) =
      (9 : ℂ) • canonicalBlock (factorialScale 8) k306occ
        (complexify c304desc6 *ᵥ x) := by
  rw [k307_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c304desc7_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c304desc8_lower_matrix :
    b308lower * c304desc8 = (12 : ℚ) • c304desc7 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c304desc8_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k308occ
      (complexify c304desc8 *ᵥ x)) =
      (12 : ℂ) • canonicalBlock (factorialScale 8) k307occ
        (complexify c304desc7 *ᵥ x) := by
  rw [k308_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c304desc8_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c305desc6_lower_matrix :
    b306lower * c305desc6 = (3 : ℚ) • c305desc5 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c305desc6_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k306occ
      (complexify c305desc6 *ᵥ x)) =
      (3 : ℂ) • canonicalBlock (factorialScale 8) k305occ
        (complexify c305desc5 *ᵥ x) := by
  rw [k306_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c305desc6_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c305desc7_lower_matrix :
    b307lower * c305desc7 = (6 : ℚ) • c305desc6 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c305desc7_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k307occ
      (complexify c305desc7 *ᵥ x)) =
      (6 : ℂ) • canonicalBlock (factorialScale 8) k306occ
        (complexify c305desc6 *ᵥ x) := by
  rw [k307_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c305desc7_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c305desc8_lower_matrix :
    b308lower * c305desc8 = (9 : ℚ) • c305desc7 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c305desc8_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k308occ
      (complexify c305desc8 *ᵥ x)) =
      (9 : ℂ) • canonicalBlock (factorialScale 8) k307occ
        (complexify c305desc7 *ᵥ x) := by
  rw [k308_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c305desc8_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c306desc7_lower_matrix :
    b307lower * c306desc7 = (3 : ℚ) • c306desc6 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c306desc7_actual_lower (x : Fin 2 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k307occ
      (complexify c306desc7 *ᵥ x)) =
      (3 : ℂ) • canonicalBlock (factorialScale 8) k306occ
        (complexify c306desc6 *ᵥ x) := by
  rw [k307_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c306desc7_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c306desc8_lower_matrix :
    b308lower * c306desc8 = (6 : ℚ) • c306desc7 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c306desc8_actual_lower (x : Fin 2 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k308occ
      (complexify c306desc8 *ᵥ x)) =
      (6 : ℂ) • canonicalBlock (factorialScale 8) k307occ
        (complexify c306desc7 *ᵥ x) := by
  rw [k308_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c306desc8_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- Exact rational table identity; independently checked in the Lean kernel. -/
theorem c307desc8_lower_matrix :
    b308lower * c307desc8 = (3 : ℚ) • c307desc7 := by decide +kernel

/-- Actual total lowering on actual COM descendants: L R^k = 3k R^(k-1). -/
theorem c307desc8_actual_lower (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalBlock (factorialScale 8) k308occ
      (complexify c307desc8 *ᵥ x)) =
      (3 : ℂ) • canonicalBlock (factorialScale 8) k307occ
        (complexify c307desc7 *ᵥ x) := by
  rw [k308_actual_lower_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    c307desc8_lower_matrix, lower_complexify_smul_rat, Matrix.smul_mulVec,
    canonicalBlock_smul9]
  norm_num

/-- CCR on the entire source degree block, before the finite upper boundary. -/
theorem k300_ccr_matrix :
    b301lower * c300raise0 = (3 : ℚ) • (1 : Matrix (Fin 1) (Fin 1) ℚ) := by decide +kernel

theorem k300_actual_ccr (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalCOMRaise9 (canonicalBlock (factorialScale 8) k300occ x)) =
      canonicalCOMRaise9 (canonicalCOMLower9 (canonicalBlock (factorialScale 8) k300occ x)) +
        (3 : ℂ) • canonicalBlock (factorialScale 8) k300occ x := by
  rw [k300_actual_raise_block, k301_actual_lower_block, k300_actual_lower_block,
    map_zero, zero_add, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    k300_ccr_matrix, lower_complexify_smul_rat, complexify_one_rat,
    Matrix.smul_mulVec, Matrix.one_mulVec, canonicalBlock_smul9]
  norm_num

/-- CCR on the entire source degree block, before the finite upper boundary. -/
theorem k301_ccr_matrix :
    b302lower * c300raise1 = c300raise0 * b301lower + (3 : ℚ) • (1 : Matrix (Fin 1) (Fin 1) ℚ) := by decide +kernel

theorem k301_actual_ccr (x : Fin 1 → ℂ) :
    canonicalCOMLower9 (canonicalCOMRaise9 (canonicalBlock (factorialScale 8) k301occ x)) =
      canonicalCOMRaise9 (canonicalCOMLower9 (canonicalBlock (factorialScale 8) k301occ x)) +
        (3 : ℂ) • canonicalBlock (factorialScale 8) k301occ x := by
  rw [k301_actual_raise_block, k302_actual_lower_block,
    k301_actual_lower_block, k300_actual_raise_block,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← complexify_mul_rect, ← complexify_mul_rect, k301_ccr_matrix,
    lower_complexify_add_rect, lower_complexify_smul_rat, complexify_one_rat,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    canonicalBlock_add9, canonicalBlock_smul9]
  norm_num

/-- CCR on the entire source degree block, before the finite upper boundary. -/
theorem k302_ccr_matrix :
    b303lower * c300raise2 = c300raise1 * b302lower + (3 : ℚ) • (1 : Matrix (Fin 2) (Fin 2) ℚ) := by decide +kernel

theorem k302_actual_ccr (x : Fin 2 → ℂ) :
    canonicalCOMLower9 (canonicalCOMRaise9 (canonicalBlock (factorialScale 8) k302occ x)) =
      canonicalCOMRaise9 (canonicalCOMLower9 (canonicalBlock (factorialScale 8) k302occ x)) +
        (3 : ℂ) • canonicalBlock (factorialScale 8) k302occ x := by
  rw [k302_actual_raise_block, k303_actual_lower_block,
    k302_actual_lower_block, k301_actual_raise_block,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← complexify_mul_rect, ← complexify_mul_rect, k302_ccr_matrix,
    lower_complexify_add_rect, lower_complexify_smul_rat, complexify_one_rat,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    canonicalBlock_add9, canonicalBlock_smul9]
  norm_num

/-- CCR on the entire source degree block, before the finite upper boundary. -/
theorem k303_ccr_matrix :
    b304lower * c300raise3 = c300raise2 * b303lower + (3 : ℚ) • (1 : Matrix (Fin 3) (Fin 3) ℚ) := by decide +kernel

theorem k303_actual_ccr (x : Fin 3 → ℂ) :
    canonicalCOMLower9 (canonicalCOMRaise9 (canonicalBlock (factorialScale 8) k303occ x)) =
      canonicalCOMRaise9 (canonicalCOMLower9 (canonicalBlock (factorialScale 8) k303occ x)) +
        (3 : ℂ) • canonicalBlock (factorialScale 8) k303occ x := by
  rw [k303_actual_raise_block, k304_actual_lower_block,
    k303_actual_lower_block, k302_actual_raise_block,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← complexify_mul_rect, ← complexify_mul_rect, k303_ccr_matrix,
    lower_complexify_add_rect, lower_complexify_smul_rat, complexify_one_rat,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    canonicalBlock_add9, canonicalBlock_smul9]
  norm_num

/-- CCR on the entire source degree block, before the finite upper boundary. -/
theorem k304_ccr_matrix :
    b305lower * c300raise4 = c300raise3 * b304lower + (3 : ℚ) • (1 : Matrix (Fin 4) (Fin 4) ℚ) := by decide +kernel

theorem k304_actual_ccr (x : Fin 4 → ℂ) :
    canonicalCOMLower9 (canonicalCOMRaise9 (canonicalBlock (factorialScale 8) k304occ x)) =
      canonicalCOMRaise9 (canonicalCOMLower9 (canonicalBlock (factorialScale 8) k304occ x)) +
        (3 : ℂ) • canonicalBlock (factorialScale 8) k304occ x := by
  rw [k304_actual_raise_block, k305_actual_lower_block,
    k304_actual_lower_block, k303_actual_raise_block,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← complexify_mul_rect, ← complexify_mul_rect, k304_ccr_matrix,
    lower_complexify_add_rect, lower_complexify_smul_rat, complexify_one_rat,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    canonicalBlock_add9, canonicalBlock_smul9]
  norm_num

/-- CCR on the entire source degree block, before the finite upper boundary. -/
theorem k305_ccr_matrix :
    b306lower * c300raise5 = c300raise4 * b305lower + (3 : ℚ) • (1 : Matrix (Fin 5) (Fin 5) ℚ) := by decide +kernel

theorem k305_actual_ccr (x : Fin 5 → ℂ) :
    canonicalCOMLower9 (canonicalCOMRaise9 (canonicalBlock (factorialScale 8) k305occ x)) =
      canonicalCOMRaise9 (canonicalCOMLower9 (canonicalBlock (factorialScale 8) k305occ x)) +
        (3 : ℂ) • canonicalBlock (factorialScale 8) k305occ x := by
  rw [k305_actual_raise_block, k306_actual_lower_block,
    k305_actual_lower_block, k304_actual_raise_block,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← complexify_mul_rect, ← complexify_mul_rect, k305_ccr_matrix,
    lower_complexify_add_rect, lower_complexify_smul_rat, complexify_one_rat,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    canonicalBlock_add9, canonicalBlock_smul9]
  norm_num

/-- CCR on the entire source degree block, before the finite upper boundary. -/
theorem k306_ccr_matrix :
    b307lower * c300raise6 = c300raise5 * b306lower + (3 : ℚ) • (1 : Matrix (Fin 7) (Fin 7) ℚ) := by decide +kernel

theorem k306_actual_ccr (x : Fin 7 → ℂ) :
    canonicalCOMLower9 (canonicalCOMRaise9 (canonicalBlock (factorialScale 8) k306occ x)) =
      canonicalCOMRaise9 (canonicalCOMLower9 (canonicalBlock (factorialScale 8) k306occ x)) +
        (3 : ℂ) • canonicalBlock (factorialScale 8) k306occ x := by
  rw [k306_actual_raise_block, k307_actual_lower_block,
    k306_actual_lower_block, k305_actual_raise_block,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← complexify_mul_rect, ← complexify_mul_rect, k306_ccr_matrix,
    lower_complexify_add_rect, lower_complexify_smul_rat, complexify_one_rat,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    canonicalBlock_add9, canonicalBlock_smul9]
  norm_num

/-- CCR on the entire source degree block, before the finite upper boundary. -/
theorem k307_ccr_matrix :
    b308lower * c300raise7 = c300raise6 * b307lower + (3 : ℚ) • (1 : Matrix (Fin 8) (Fin 8) ℚ) := by decide +kernel

theorem k307_actual_ccr (x : Fin 8 → ℂ) :
    canonicalCOMLower9 (canonicalCOMRaise9 (canonicalBlock (factorialScale 8) k307occ x)) =
      canonicalCOMRaise9 (canonicalCOMLower9 (canonicalBlock (factorialScale 8) k307occ x)) +
        (3 : ℂ) • canonicalBlock (factorialScale 8) k307occ x := by
  rw [k307_actual_raise_block, k308_actual_lower_block,
    k307_actual_lower_block, k306_actual_raise_block,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← complexify_mul_rect, ← complexify_mul_rect, k307_ccr_matrix,
    lower_complexify_add_rect, lower_complexify_smul_rat, complexify_one_rat,
    Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    canonicalBlock_add9, canonicalBlock_smul9]
  norm_num

#print axioms finitePaperLower9_word
#print axioms canonicalCOMLower9_scaledWord
#print axioms complexify_zero_rect
#print axioms lower_complexify_add_rect
#print axioms lower_complexify_smul_rat
#print axioms canonicalBlock_zero9
#print axioms canonicalBlock_add9
#print axioms canonicalBlock_smul9
#print axioms k300_paper_lower_word
#print axioms k300_actual_canonical_lower
#print axioms k300_actual_lower_block
#print axioms k301_paper_lower_word
#print axioms k301_actual_canonical_lower
#print axioms k301_actual_lower_block
#print axioms k302_paper_lower_word
#print axioms k302_actual_canonical_lower
#print axioms k302_actual_lower_block
#print axioms k303_paper_lower_word
#print axioms k303_actual_canonical_lower
#print axioms k303_actual_lower_block
#print axioms k304_paper_lower_word
#print axioms k304_actual_canonical_lower
#print axioms k304_actual_lower_block
#print axioms k305_paper_lower_word
#print axioms k305_actual_canonical_lower
#print axioms k305_actual_lower_block
#print axioms k306_paper_lower_word
#print axioms k306_actual_canonical_lower
#print axioms k306_actual_lower_block
#print axioms k307_paper_lower_word
#print axioms k307_actual_canonical_lower
#print axioms k307_actual_lower_block
#print axioms k308_paper_lower_word
#print axioms k308_actual_canonical_lower
#print axioms k308_actual_lower_block
#print axioms k300_actual_relative_vacuum
#print axioms k301_actual_relative_vacuum
#print axioms k302_actual_relative_vacuum
#print axioms k303_actual_relative_vacuum
#print axioms k304_actual_relative_vacuum
#print axioms k305_actual_relative_vacuum
#print axioms k306_actual_relative_vacuum
#print axioms k307_actual_relative_vacuum
#print axioms k308_actual_relative_vacuum
#print axioms c300desc1_lower_matrix
#print axioms c300desc1_actual_lower
#print axioms c300desc2_lower_matrix
#print axioms c300desc2_actual_lower
#print axioms c300desc3_lower_matrix
#print axioms c300desc3_actual_lower
#print axioms c300desc4_lower_matrix
#print axioms c300desc4_actual_lower
#print axioms c300desc5_lower_matrix
#print axioms c300desc5_actual_lower
#print axioms c300desc6_lower_matrix
#print axioms c300desc6_actual_lower
#print axioms c300desc7_lower_matrix
#print axioms c300desc7_actual_lower
#print axioms c300desc8_lower_matrix
#print axioms c300desc8_actual_lower
#print axioms c301desc2_lower_matrix
#print axioms c301desc2_actual_lower
#print axioms c301desc3_lower_matrix
#print axioms c301desc3_actual_lower
#print axioms c301desc4_lower_matrix
#print axioms c301desc4_actual_lower
#print axioms c301desc5_lower_matrix
#print axioms c301desc5_actual_lower
#print axioms c301desc6_lower_matrix
#print axioms c301desc6_actual_lower
#print axioms c301desc7_lower_matrix
#print axioms c301desc7_actual_lower
#print axioms c301desc8_lower_matrix
#print axioms c301desc8_actual_lower
#print axioms c302desc3_lower_matrix
#print axioms c302desc3_actual_lower
#print axioms c302desc4_lower_matrix
#print axioms c302desc4_actual_lower
#print axioms c302desc5_lower_matrix
#print axioms c302desc5_actual_lower
#print axioms c302desc6_lower_matrix
#print axioms c302desc6_actual_lower
#print axioms c302desc7_lower_matrix
#print axioms c302desc7_actual_lower
#print axioms c302desc8_lower_matrix
#print axioms c302desc8_actual_lower
#print axioms c303desc4_lower_matrix
#print axioms c303desc4_actual_lower
#print axioms c303desc5_lower_matrix
#print axioms c303desc5_actual_lower
#print axioms c303desc6_lower_matrix
#print axioms c303desc6_actual_lower
#print axioms c303desc7_lower_matrix
#print axioms c303desc7_actual_lower
#print axioms c303desc8_lower_matrix
#print axioms c303desc8_actual_lower
#print axioms c304desc5_lower_matrix
#print axioms c304desc5_actual_lower
#print axioms c304desc6_lower_matrix
#print axioms c304desc6_actual_lower
#print axioms c304desc7_lower_matrix
#print axioms c304desc7_actual_lower
#print axioms c304desc8_lower_matrix
#print axioms c304desc8_actual_lower
#print axioms c305desc6_lower_matrix
#print axioms c305desc6_actual_lower
#print axioms c305desc7_lower_matrix
#print axioms c305desc7_actual_lower
#print axioms c305desc8_lower_matrix
#print axioms c305desc8_actual_lower
#print axioms c306desc7_lower_matrix
#print axioms c306desc7_actual_lower
#print axioms c306desc8_lower_matrix
#print axioms c306desc8_actual_lower
#print axioms c307desc8_lower_matrix
#print axioms c307desc8_actual_lower
#print axioms k300_ccr_matrix
#print axioms k300_actual_ccr
#print axioms k301_ccr_matrix
#print axioms k301_actual_ccr
#print axioms k302_ccr_matrix
#print axioms k302_actual_ccr
#print axioms k303_ccr_matrix
#print axioms k303_actual_ccr
#print axioms k304_ccr_matrix
#print axioms k304_actual_ccr
#print axioms k305_ccr_matrix
#print axioms k305_actual_ccr
#print axioms k306_ccr_matrix
#print axioms k306_actual_ccr
#print axioms k307_ccr_matrix
#print axioms k307_actual_ccr
end TorusLean.BosonFiniteCertificate
