import torus.shared.BosonFiniteCertificateCanonicalTransport
import torus.shared.BosonFiniteCertificateCanonicalGram

/-! The stored finite COM matrices act by genuine polynomial raising.
This is the unnormalized total COM generator (no extra 1/sqrt(3)). Only
source degrees 0,...,7 and descendants through degree 8 are identified;
no zero extension is asserted to equal an unrestricted physical operator. -/
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

def raiseSource9 (j : Fin 8) : Fin 9 := ⟨j.val, by omega⟩
def raiseTarget9 (j : Fin 8) : Fin 9 := ⟨j.val+1, by omega⟩

/-- Literal sum of creator/derivative words, on the whole finite-variable core. -/
def finitePaperRaise9 : Core (Fin 9) ℂ →ₗ[ℂ] Core (Fin 9) ℂ :=
  ∑ j : Fin 8, normalWord [raiseTarget9 j] [raiseSource9 j]

/-- Invertible factorial change of variables of the genuine raising operator. -/
def canonicalCOMRaise9 : Core (Fin 9) ℂ →ₗ[ℂ] Core (Fin 9) ℂ :=
  conjugateOperator factorialRoot9 factorialRoot9_ne_zero finitePaperRaise9

/-- Every coefficient is the actual bosonic multiplicity count, including
repeated orbitals; there is no (j+1) multiplier in the paper coordinates. -/
theorem finitePaperRaise9_word (s : List (Fin 9)) :
    finitePaperRaise9 (wordPolynomial s) =
      ∑ j : Fin 8, (s.count (raiseSource9 j) : ℂ) •
        wordPolynomial (raiseTarget9 j :: s.erase (raiseSource9 j)) := by
  simp [finitePaperRaise9, LinearMap.sum_apply, normalWord_wordPolynomial,
    wordRemovalWeight, eraseWord]

theorem canonicalCOMRaise9_scaledWord (s : List (Fin 9)) :
    canonicalCOMRaise9 (scaledWord factorialRoot9 s) =
      ∑ j : Fin 8, (s.count (raiseSource9 j) : ℂ) •
        scaledWord factorialRoot9 (raiseTarget9 j :: s.erase (raiseSource9 j)) := by
  rw [canonicalCOMRaise9, ← rescaleEquiv_word factorialRoot9 factorialRoot9_ne_zero,
    conjugateOperator_apply_rescale, finitePaperRaise9_word, map_sum]
  simp only [map_smul, rescaleEquiv_word]

/-- Rectangular synthesis, for a real operator with proved basis actions. -/
theorem canonicalBlock_rect_action {m n : ℕ}
    (src : Fin n → (Fin 9 →₀ ℕ)) (dst : Fin m → (Fin 9 →₀ ℕ))
    (A : Core (Fin 9) ℂ →ₗ[ℂ] Core (Fin 9) ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hA : ∀ a, A (canonicalMonomial (factorialScale 8) (src a)) =
      ∑ b, M b a • canonicalMonomial (factorialScale 8) (dst b)) (x : Fin n → ℂ) :
    A (canonicalBlock (factorialScale 8) src x) =
      canonicalBlock (factorialScale 8) dst (M *ᵥ x) := by
  simp only [canonicalBlock, map_sum, map_smul, hA, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, mul_comm]

#print axioms finitePaperRaise9_word
#print axioms canonicalCOMRaise9_scaledWord
#print axioms canonicalBlock_rect_action

theorem k300_paper_raise_word (a : Fin 1) :
    finitePaperRaise9 (wordPolynomial ((p300basis a).map fin9)) =
      ∑ i : Fin 1, (c300raise0 i a : ℂ) •
        wordPolynomial ((p301basis i).map fin9) := by
  fin_cases a <;>
    simp only [finitePaperRaise9, LinearMap.sum_apply, normalWord_wordPolynomial] <;>
    norm_num [Fin.sum_univ_succ, p300basis, p301basis, c300raise0, raisingEntry, List.eraseDups_cons,
      wordRemovalWeight, eraseWord, wordPolynomial, raiseSource9, raiseTarget9,
      fin9, Algebra.smul_def] <;> (try simp only [map_ofNat]) <;> ring

theorem k300_actual_canonical_raise (a : Fin 1) :
    canonicalCOMRaise9 (canonicalMonomial (factorialScale 8) (k300occ a)) =
      ∑ i : Fin 1, (c300raise0 i a : ℂ) •
        canonicalMonomial (factorialScale 8) (k301occ i) := by
  rw [canonicalCOMRaise9, ← k300_canonical_source_word,
    ← rescaleEquiv_word factorialRoot9 factorialRoot9_ne_zero,
    conjugateOperator_apply_rescale, k300_paper_raise_word, map_sum]
  simp only [map_smul, rescaleEquiv_word, k301_canonical_source_word]

theorem k300_actual_raise_block (x : Fin 1 → ℂ) :
    canonicalCOMRaise9 (canonicalBlock (factorialScale 8) k300occ x) =
      canonicalBlock (factorialScale 8) k301occ (complexify c300raise0 *ᵥ x) := by
  exact canonicalBlock_rect_action k300occ k301occ canonicalCOMRaise9
    (complexify c300raise0) k300_actual_canonical_raise x

#print axioms k300_paper_raise_word
#print axioms k300_actual_canonical_raise
#print axioms k300_actual_raise_block

theorem k301_paper_raise_word (a : Fin 1) :
    finitePaperRaise9 (wordPolynomial ((p301basis a).map fin9)) =
      ∑ i : Fin 2, (c300raise1 i a : ℂ) •
        wordPolynomial ((p302basis i).map fin9) := by
  fin_cases a <;>
    simp only [finitePaperRaise9, LinearMap.sum_apply, normalWord_wordPolynomial] <;>
    norm_num [Fin.sum_univ_succ, p301basis, p302basis, c300raise1, raisingEntry, List.eraseDups_cons,
      wordRemovalWeight, eraseWord, wordPolynomial, raiseSource9, raiseTarget9,
      fin9, Algebra.smul_def] <;> (try simp only [map_ofNat]) <;> ring

theorem k301_actual_canonical_raise (a : Fin 1) :
    canonicalCOMRaise9 (canonicalMonomial (factorialScale 8) (k301occ a)) =
      ∑ i : Fin 2, (c300raise1 i a : ℂ) •
        canonicalMonomial (factorialScale 8) (k302occ i) := by
  rw [canonicalCOMRaise9, ← k301_canonical_source_word,
    ← rescaleEquiv_word factorialRoot9 factorialRoot9_ne_zero,
    conjugateOperator_apply_rescale, k301_paper_raise_word, map_sum]
  simp only [map_smul, rescaleEquiv_word, k302_canonical_source_word]

theorem k301_actual_raise_block (x : Fin 1 → ℂ) :
    canonicalCOMRaise9 (canonicalBlock (factorialScale 8) k301occ x) =
      canonicalBlock (factorialScale 8) k302occ (complexify c300raise1 *ᵥ x) := by
  exact canonicalBlock_rect_action k301occ k302occ canonicalCOMRaise9
    (complexify c300raise1) k301_actual_canonical_raise x

#print axioms k301_paper_raise_word
#print axioms k301_actual_canonical_raise
#print axioms k301_actual_raise_block

theorem k302_paper_raise_word (a : Fin 2) :
    finitePaperRaise9 (wordPolynomial ((p302basis a).map fin9)) =
      ∑ i : Fin 3, (c300raise2 i a : ℂ) •
        wordPolynomial ((p303basis i).map fin9) := by
  fin_cases a <;>
    simp only [finitePaperRaise9, LinearMap.sum_apply, normalWord_wordPolynomial] <;>
    norm_num [Fin.sum_univ_succ, p302basis, p303basis, c300raise2, raisingEntry, List.eraseDups_cons,
      wordRemovalWeight, eraseWord, wordPolynomial, raiseSource9, raiseTarget9,
      fin9, Algebra.smul_def] <;> (try simp only [map_ofNat]) <;> ring

theorem k302_actual_canonical_raise (a : Fin 2) :
    canonicalCOMRaise9 (canonicalMonomial (factorialScale 8) (k302occ a)) =
      ∑ i : Fin 3, (c300raise2 i a : ℂ) •
        canonicalMonomial (factorialScale 8) (k303occ i) := by
  rw [canonicalCOMRaise9, ← k302_canonical_source_word,
    ← rescaleEquiv_word factorialRoot9 factorialRoot9_ne_zero,
    conjugateOperator_apply_rescale, k302_paper_raise_word, map_sum]
  simp only [map_smul, rescaleEquiv_word, k303_canonical_source_word]

theorem k302_actual_raise_block (x : Fin 2 → ℂ) :
    canonicalCOMRaise9 (canonicalBlock (factorialScale 8) k302occ x) =
      canonicalBlock (factorialScale 8) k303occ (complexify c300raise2 *ᵥ x) := by
  exact canonicalBlock_rect_action k302occ k303occ canonicalCOMRaise9
    (complexify c300raise2) k302_actual_canonical_raise x

#print axioms k302_paper_raise_word
#print axioms k302_actual_canonical_raise
#print axioms k302_actual_raise_block

theorem k303_paper_raise_word (a : Fin 3) :
    finitePaperRaise9 (wordPolynomial ((p303basis a).map fin9)) =
      ∑ i : Fin 4, (c300raise3 i a : ℂ) •
        wordPolynomial ((p304basis i).map fin9) := by
  fin_cases a <;>
    simp only [finitePaperRaise9, LinearMap.sum_apply, normalWord_wordPolynomial] <;>
    norm_num [Fin.sum_univ_succ, p303basis, p304basis, c300raise3, raisingEntry, List.eraseDups_cons,
      wordRemovalWeight, eraseWord, wordPolynomial, raiseSource9, raiseTarget9,
      fin9, Algebra.smul_def] <;> (try simp only [map_ofNat]) <;> ring

theorem k303_actual_canonical_raise (a : Fin 3) :
    canonicalCOMRaise9 (canonicalMonomial (factorialScale 8) (k303occ a)) =
      ∑ i : Fin 4, (c300raise3 i a : ℂ) •
        canonicalMonomial (factorialScale 8) (k304occ i) := by
  rw [canonicalCOMRaise9, ← k303_canonical_source_word,
    ← rescaleEquiv_word factorialRoot9 factorialRoot9_ne_zero,
    conjugateOperator_apply_rescale, k303_paper_raise_word, map_sum]
  simp only [map_smul, rescaleEquiv_word, k304_canonical_source_word]

theorem k303_actual_raise_block (x : Fin 3 → ℂ) :
    canonicalCOMRaise9 (canonicalBlock (factorialScale 8) k303occ x) =
      canonicalBlock (factorialScale 8) k304occ (complexify c300raise3 *ᵥ x) := by
  exact canonicalBlock_rect_action k303occ k304occ canonicalCOMRaise9
    (complexify c300raise3) k303_actual_canonical_raise x

#print axioms k303_paper_raise_word
#print axioms k303_actual_canonical_raise
#print axioms k303_actual_raise_block

theorem k304_paper_raise_word (a : Fin 4) :
    finitePaperRaise9 (wordPolynomial ((p304basis a).map fin9)) =
      ∑ i : Fin 5, (c300raise4 i a : ℂ) •
        wordPolynomial ((p305basis i).map fin9) := by
  fin_cases a <;>
    simp only [finitePaperRaise9, LinearMap.sum_apply, normalWord_wordPolynomial] <;>
    norm_num [Fin.sum_univ_succ, p304basis, p305basis, c300raise4, raisingEntry, List.eraseDups_cons,
      wordRemovalWeight, eraseWord, wordPolynomial, raiseSource9, raiseTarget9,
      fin9, Algebra.smul_def] <;> (try simp only [map_ofNat]) <;> ring

theorem k304_actual_canonical_raise (a : Fin 4) :
    canonicalCOMRaise9 (canonicalMonomial (factorialScale 8) (k304occ a)) =
      ∑ i : Fin 5, (c300raise4 i a : ℂ) •
        canonicalMonomial (factorialScale 8) (k305occ i) := by
  rw [canonicalCOMRaise9, ← k304_canonical_source_word,
    ← rescaleEquiv_word factorialRoot9 factorialRoot9_ne_zero,
    conjugateOperator_apply_rescale, k304_paper_raise_word, map_sum]
  simp only [map_smul, rescaleEquiv_word, k305_canonical_source_word]

theorem k304_actual_raise_block (x : Fin 4 → ℂ) :
    canonicalCOMRaise9 (canonicalBlock (factorialScale 8) k304occ x) =
      canonicalBlock (factorialScale 8) k305occ (complexify c300raise4 *ᵥ x) := by
  exact canonicalBlock_rect_action k304occ k305occ canonicalCOMRaise9
    (complexify c300raise4) k304_actual_canonical_raise x

#print axioms k304_paper_raise_word
#print axioms k304_actual_canonical_raise
#print axioms k304_actual_raise_block

theorem k305_paper_raise_word (a : Fin 5) :
    finitePaperRaise9 (wordPolynomial ((p305basis a).map fin9)) =
      ∑ i : Fin 7, (c300raise5 i a : ℂ) •
        wordPolynomial ((p306basis i).map fin9) := by
  fin_cases a <;>
    simp only [finitePaperRaise9, LinearMap.sum_apply, normalWord_wordPolynomial] <;>
    norm_num [Fin.sum_univ_succ, p305basis, p306basis, c300raise5, raisingEntry, List.eraseDups_cons,
      wordRemovalWeight, eraseWord, wordPolynomial, raiseSource9, raiseTarget9,
      fin9, Algebra.smul_def] <;> (try simp only [map_ofNat]) <;> ring

theorem k305_actual_canonical_raise (a : Fin 5) :
    canonicalCOMRaise9 (canonicalMonomial (factorialScale 8) (k305occ a)) =
      ∑ i : Fin 7, (c300raise5 i a : ℂ) •
        canonicalMonomial (factorialScale 8) (k306occ i) := by
  rw [canonicalCOMRaise9, ← k305_canonical_source_word,
    ← rescaleEquiv_word factorialRoot9 factorialRoot9_ne_zero,
    conjugateOperator_apply_rescale, k305_paper_raise_word, map_sum]
  simp only [map_smul, rescaleEquiv_word, k306_canonical_source_word]

theorem k305_actual_raise_block (x : Fin 5 → ℂ) :
    canonicalCOMRaise9 (canonicalBlock (factorialScale 8) k305occ x) =
      canonicalBlock (factorialScale 8) k306occ (complexify c300raise5 *ᵥ x) := by
  exact canonicalBlock_rect_action k305occ k306occ canonicalCOMRaise9
    (complexify c300raise5) k305_actual_canonical_raise x

#print axioms k305_paper_raise_word
#print axioms k305_actual_canonical_raise
#print axioms k305_actual_raise_block

theorem k306_paper_raise_word (a : Fin 7) :
    finitePaperRaise9 (wordPolynomial ((p306basis a).map fin9)) =
      ∑ i : Fin 8, (c300raise6 i a : ℂ) •
        wordPolynomial ((p307basis i).map fin9) := by
  fin_cases a <;>
    simp only [finitePaperRaise9, LinearMap.sum_apply, normalWord_wordPolynomial] <;>
    norm_num [Fin.sum_univ_succ, p306basis, p307basis, c300raise6, raisingEntry, List.eraseDups_cons,
      wordRemovalWeight, eraseWord, wordPolynomial, raiseSource9, raiseTarget9,
      fin9, Algebra.smul_def] <;> (try simp only [map_ofNat]) <;> ring

theorem k306_actual_canonical_raise (a : Fin 7) :
    canonicalCOMRaise9 (canonicalMonomial (factorialScale 8) (k306occ a)) =
      ∑ i : Fin 8, (c300raise6 i a : ℂ) •
        canonicalMonomial (factorialScale 8) (k307occ i) := by
  rw [canonicalCOMRaise9, ← k306_canonical_source_word,
    ← rescaleEquiv_word factorialRoot9 factorialRoot9_ne_zero,
    conjugateOperator_apply_rescale, k306_paper_raise_word, map_sum]
  simp only [map_smul, rescaleEquiv_word, k307_canonical_source_word]

theorem k306_actual_raise_block (x : Fin 7 → ℂ) :
    canonicalCOMRaise9 (canonicalBlock (factorialScale 8) k306occ x) =
      canonicalBlock (factorialScale 8) k307occ (complexify c300raise6 *ᵥ x) := by
  exact canonicalBlock_rect_action k306occ k307occ canonicalCOMRaise9
    (complexify c300raise6) k306_actual_canonical_raise x

#print axioms k306_paper_raise_word
#print axioms k306_actual_canonical_raise
#print axioms k306_actual_raise_block

theorem k307_paper_raise_word (a : Fin 8) :
    finitePaperRaise9 (wordPolynomial ((p307basis a).map fin9)) =
      ∑ i : Fin 10, (c300raise7 i a : ℂ) •
        wordPolynomial ((p308basis i).map fin9) := by
  fin_cases a <;>
    simp only [finitePaperRaise9, LinearMap.sum_apply, normalWord_wordPolynomial] <;>
    norm_num [Fin.sum_univ_succ, p307basis, p308basis, c300raise7, raisingEntry, List.eraseDups_cons,
      wordRemovalWeight, eraseWord, wordPolynomial, raiseSource9, raiseTarget9,
      fin9, Algebra.smul_def] <;> (try simp only [map_ofNat]) <;> ring

theorem k307_actual_canonical_raise (a : Fin 8) :
    canonicalCOMRaise9 (canonicalMonomial (factorialScale 8) (k307occ a)) =
      ∑ i : Fin 10, (c300raise7 i a : ℂ) •
        canonicalMonomial (factorialScale 8) (k308occ i) := by
  rw [canonicalCOMRaise9, ← k307_canonical_source_word,
    ← rescaleEquiv_word factorialRoot9 factorialRoot9_ne_zero,
    conjugateOperator_apply_rescale, k307_paper_raise_word, map_sum]
  simp only [map_smul, rescaleEquiv_word, k308_canonical_source_word]

theorem k307_actual_raise_block (x : Fin 8 → ℂ) :
    canonicalCOMRaise9 (canonicalBlock (factorialScale 8) k307occ x) =
      canonicalBlock (factorialScale 8) k308occ (complexify c300raise7 *ᵥ x) := by
  exact canonicalBlock_rect_action k307occ k308occ canonicalCOMRaise9
    (complexify c300raise7) k307_actual_canonical_raise x

#print axioms k307_paper_raise_word
#print axioms k307_actual_canonical_raise
#print axioms k307_actual_raise_block

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c300desc0_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0]
      (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k300occ (complexify c300desc0 *ᵥ x) := by
  rw [Function.iterate_zero_apply, c300desc0_root]

#print axioms c300desc0_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c300desc1_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[1]
      (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k301occ (complexify c300desc1 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c300desc0_actual,
    k300_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise0 * c300desc0 = c300desc1 from c300desc1_step]

#print axioms c300desc1_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c300desc2_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[2]
      (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k302occ (complexify c300desc2 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c300desc1_actual,
    k301_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise1 * c300desc1 = c300desc2 from c300desc2_step]

#print axioms c300desc2_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c300desc3_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[3]
      (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k303occ (complexify c300desc3 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c300desc2_actual,
    k302_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise2 * c300desc2 = c300desc3 from c300desc3_step]

#print axioms c300desc3_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c300desc4_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[4]
      (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k304occ (complexify c300desc4 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c300desc3_actual,
    k303_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise3 * c300desc3 = c300desc4 from c300desc4_step]

#print axioms c300desc4_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c300desc5_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[5]
      (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k305occ (complexify c300desc5 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c300desc4_actual,
    k304_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise4 * c300desc4 = c300desc5 from c300desc5_step]

#print axioms c300desc5_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c300desc6_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[6]
      (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k306occ (complexify c300desc6 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c300desc5_actual,
    k305_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise5 * c300desc5 = c300desc6 from c300desc6_step]

#print axioms c300desc6_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c300desc7_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[7]
      (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k307occ (complexify c300desc7 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c300desc6_actual,
    k306_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise6 * c300desc6 = c300desc7 from c300desc7_step]

#print axioms c300desc7_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c300desc8_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[8]
      (canonicalBlock (factorialScale 8) k300occ (complexify b300relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k308occ (complexify c300desc8 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c300desc7_actual,
    k307_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise7 * c300desc7 = c300desc8 from c300desc8_step]

#print axioms c300desc8_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c301desc1_actual (x : Fin 0 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0]
      (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k301occ (complexify c301desc1 *ᵥ x) := by
  rw [Function.iterate_zero_apply, c301desc1_root]

#print axioms c301desc1_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c301desc2_actual (x : Fin 0 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[1]
      (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k302occ (complexify c301desc2 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c301desc1_actual,
    k301_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise1 * c301desc1 = c301desc2 from c301desc2_step]

#print axioms c301desc2_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c301desc3_actual (x : Fin 0 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[2]
      (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k303occ (complexify c301desc3 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c301desc2_actual,
    k302_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise2 * c301desc2 = c301desc3 from c301desc3_step]

#print axioms c301desc3_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c301desc4_actual (x : Fin 0 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[3]
      (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k304occ (complexify c301desc4 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c301desc3_actual,
    k303_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise3 * c301desc3 = c301desc4 from c301desc4_step]

#print axioms c301desc4_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c301desc5_actual (x : Fin 0 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[4]
      (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k305occ (complexify c301desc5 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c301desc4_actual,
    k304_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise4 * c301desc4 = c301desc5 from c301desc5_step]

#print axioms c301desc5_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c301desc6_actual (x : Fin 0 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[5]
      (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k306occ (complexify c301desc6 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c301desc5_actual,
    k305_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise5 * c301desc5 = c301desc6 from c301desc6_step]

#print axioms c301desc6_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c301desc7_actual (x : Fin 0 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[6]
      (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k307occ (complexify c301desc7 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c301desc6_actual,
    k306_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise6 * c301desc6 = c301desc7 from c301desc7_step]

#print axioms c301desc7_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c301desc8_actual (x : Fin 0 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[7]
      (canonicalBlock (factorialScale 8) k301occ (complexify b301relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k308occ (complexify c301desc8 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c301desc7_actual,
    k307_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise7 * c301desc7 = c301desc8 from c301desc8_step]

#print axioms c301desc8_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c302desc2_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0]
      (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k302occ (complexify c302desc2 *ᵥ x) := by
  rw [Function.iterate_zero_apply, c302desc2_root]

#print axioms c302desc2_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c302desc3_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[1]
      (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k303occ (complexify c302desc3 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c302desc2_actual,
    k302_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise2 * c302desc2 = c302desc3 from c302desc3_step]

#print axioms c302desc3_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c302desc4_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[2]
      (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k304occ (complexify c302desc4 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c302desc3_actual,
    k303_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise3 * c302desc3 = c302desc4 from c302desc4_step]

#print axioms c302desc4_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c302desc5_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[3]
      (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k305occ (complexify c302desc5 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c302desc4_actual,
    k304_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise4 * c302desc4 = c302desc5 from c302desc5_step]

#print axioms c302desc5_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c302desc6_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[4]
      (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k306occ (complexify c302desc6 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c302desc5_actual,
    k305_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise5 * c302desc5 = c302desc6 from c302desc6_step]

#print axioms c302desc6_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c302desc7_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[5]
      (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k307occ (complexify c302desc7 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c302desc6_actual,
    k306_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise6 * c302desc6 = c302desc7 from c302desc7_step]

#print axioms c302desc7_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c302desc8_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[6]
      (canonicalBlock (factorialScale 8) k302occ (complexify b302relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k308occ (complexify c302desc8 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c302desc7_actual,
    k307_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise7 * c302desc7 = c302desc8 from c302desc8_step]

#print axioms c302desc8_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c303desc3_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0]
      (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k303occ (complexify c303desc3 *ᵥ x) := by
  rw [Function.iterate_zero_apply, c303desc3_root]

#print axioms c303desc3_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c303desc4_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[1]
      (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k304occ (complexify c303desc4 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c303desc3_actual,
    k303_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise3 * c303desc3 = c303desc4 from c303desc4_step]

#print axioms c303desc4_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c303desc5_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[2]
      (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k305occ (complexify c303desc5 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c303desc4_actual,
    k304_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise4 * c303desc4 = c303desc5 from c303desc5_step]

#print axioms c303desc5_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c303desc6_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[3]
      (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k306occ (complexify c303desc6 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c303desc5_actual,
    k305_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise5 * c303desc5 = c303desc6 from c303desc6_step]

#print axioms c303desc6_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c303desc7_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[4]
      (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k307occ (complexify c303desc7 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c303desc6_actual,
    k306_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise6 * c303desc6 = c303desc7 from c303desc7_step]

#print axioms c303desc7_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c303desc8_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[5]
      (canonicalBlock (factorialScale 8) k303occ (complexify b303relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k308occ (complexify c303desc8 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c303desc7_actual,
    k307_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise7 * c303desc7 = c303desc8 from c303desc8_step]

#print axioms c303desc8_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c304desc4_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0]
      (canonicalBlock (factorialScale 8) k304occ (complexify b304relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k304occ (complexify c304desc4 *ᵥ x) := by
  rw [Function.iterate_zero_apply, c304desc4_root]

#print axioms c304desc4_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c304desc5_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[1]
      (canonicalBlock (factorialScale 8) k304occ (complexify b304relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k305occ (complexify c304desc5 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c304desc4_actual,
    k304_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise4 * c304desc4 = c304desc5 from c304desc5_step]

#print axioms c304desc5_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c304desc6_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[2]
      (canonicalBlock (factorialScale 8) k304occ (complexify b304relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k306occ (complexify c304desc6 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c304desc5_actual,
    k305_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise5 * c304desc5 = c304desc6 from c304desc6_step]

#print axioms c304desc6_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c304desc7_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[3]
      (canonicalBlock (factorialScale 8) k304occ (complexify b304relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k307occ (complexify c304desc7 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c304desc6_actual,
    k306_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise6 * c304desc6 = c304desc7 from c304desc7_step]

#print axioms c304desc7_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c304desc8_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[4]
      (canonicalBlock (factorialScale 8) k304occ (complexify b304relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k308occ (complexify c304desc8 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c304desc7_actual,
    k307_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise7 * c304desc7 = c304desc8 from c304desc8_step]

#print axioms c304desc8_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c305desc5_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0]
      (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k305occ (complexify c305desc5 *ᵥ x) := by
  rw [Function.iterate_zero_apply, c305desc5_root]

#print axioms c305desc5_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c305desc6_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[1]
      (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k306occ (complexify c305desc6 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c305desc5_actual,
    k305_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise5 * c305desc5 = c305desc6 from c305desc6_step]

#print axioms c305desc6_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c305desc7_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[2]
      (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k307occ (complexify c305desc7 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c305desc6_actual,
    k306_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise6 * c305desc6 = c305desc7 from c305desc7_step]

#print axioms c305desc7_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c305desc8_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[3]
      (canonicalBlock (factorialScale 8) k305occ (complexify b305relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k308occ (complexify c305desc8 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c305desc7_actual,
    k307_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise7 * c305desc7 = c305desc8 from c305desc8_step]

#print axioms c305desc8_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c306desc6_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0]
      (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k306occ (complexify c306desc6 *ᵥ x) := by
  rw [Function.iterate_zero_apply, c306desc6_root]

#print axioms c306desc6_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c306desc7_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[1]
      (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k307occ (complexify c306desc7 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c306desc6_actual,
    k306_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise6 * c306desc6 = c306desc7 from c306desc7_step]

#print axioms c306desc7_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c306desc8_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[2]
      (canonicalBlock (factorialScale 8) k306occ (complexify b306relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k308occ (complexify c306desc8 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c306desc7_actual,
    k307_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise7 * c306desc7 = c306desc8 from c306desc8_step]

#print axioms c306desc8_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c307desc7_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0]
      (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k307occ (complexify c307desc7 *ᵥ x) := by
  rw [Function.iterate_zero_apply, c307desc7_root]

#print axioms c307desc7_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c307desc8_actual (x : Fin 1 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[1]
      (canonicalBlock (factorialScale 8) k307occ (complexify b307relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k308occ (complexify c307desc8 *ᵥ x) := by
  rw [Function.iterate_succ_apply', c307desc7_actual,
    k307_actual_raise_block, Matrix.mulVec_mulVec, ← complexify_mul_rect,
    show c300raise7 * c307desc7 = c307desc8 from c307desc8_step]

#print axioms c307desc8_actual

/-- Stored D descendant as an iterate of the actual unnormalized COM generator. -/
theorem c308desc8_actual (x : Fin 2 → ℂ) :
    (canonicalCOMRaise9 : Core (Fin 9) ℂ → Core (Fin 9) ℂ)^[0]
      (canonicalBlock (factorialScale 8) k308occ (complexify b308relative *ᵥ x)) =
      canonicalBlock (factorialScale 8) k308occ (complexify c308desc8 *ᵥ x) := by
  rw [Function.iterate_zero_apply, c308desc8_root]

#print axioms c308desc8_actual

end TorusLean.BosonFiniteCertificate
