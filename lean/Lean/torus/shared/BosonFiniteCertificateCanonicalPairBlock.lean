import torus.shared.BosonFiniteCertificateCanonicalPairInvariant
import torus.shared.BosonFiniteCertificateCanonicalPairMembership

/-! Genuine invariance of the existing complete finite occupation blocks under
the actual pair Hamiltonian. Its matrix and square are derived only after
proving the output remains in the original block. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.Shared.BosonFiniteCertificateCanonicalPairInvariant
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.BosonFiniteCertificateCoordinate
open TorusLean.BosonFiniteCertificate
open Matrix
open scoped ComplexConjugate BigOperators

section Block
variable {B : Type*} [Fintype B] [DecidableEq B]

def canonicalOccupationSpan (occ : B → (Fin 9 →₀ ℕ)) : Submodule ℂ (Core (Fin 9) ℂ) :=
  Submodule.span ℂ (Set.range fun b => canonicalMonomial (factorialScale 8) (occ b))

private theorem list_map_sum_mem {J : Type*} (U : Submodule ℂ (Core (Fin 9) ℂ))
    (l : List J) (f : J → Core (Fin 9) ℂ) (h : ∀ j ∈ l, f j ∈ U) : (l.map f).sum ∈ U := by
  induction l with
  | nil => simpa using U.zero_mem
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact U.add_mem (h a (by simp)) (ih (fun j hj => h j (by simp [hj])))

/-- The only finite data premise is a literal occupation equality, checked for
every actual pair output in the nine membership theorems. -/
theorem pairOutputWord9_mem (d : ℕ) (occ : B → (Fin 9 →₀ ℕ))
    (hmem : ∀ p : Fin (d+1), ∀ a : Fin (p.val+1),
      ∃ b, wordOccupation (pairOutputWord9 d p.val a.val) = occ b)
    (p a : ℕ) (hp : p ≤ d) (ha : a ≤ p) :
    scaledWord pairFactorialRoot9 (pairOutputWord9 d p a) ∈ canonicalOccupationSpan occ := by
  obtain ⟨b,hb⟩ := hmem ⟨p,by omega⟩ ⟨a,by change a < p+1; omega⟩
  rw [pair_scaledWord_canonical, hb]
  exact Submodule.subset_span ⟨b,rfl⟩

theorem canonicalPairHamiltonian9_word_mem (d : ℕ) (hd : d < 9)
    (occ : B → (Fin 9 →₀ ℕ))
    (hmem : ∀ p : Fin (d+1), ∀ a : Fin (p.val+1),
      ∃ b, wordOccupation (pairOutputWord9 d p.val a.val) = occ b)
    (s : List ℕ) (hs : sourceLabelsBounded9 s = true) (hlen : s.length = 3) (hsum : s.sum = d) :
    canonicalPairHamiltonian9 d (scaledWord pairFactorialRoot9 (s.map fin9)) ∈
      canonicalOccupationSpan occ := by
  rw [canonicalPairHamiltonian9_word_action d s hd hs hlen hsum]
  apply list_map_sum_mem
  intro p hp
  apply list_map_sum_mem
  intro a ha
  apply Submodule.smul_mem
  exact pairOutputWord9_mem d occ hmem p a
    (Nat.le_of_lt_succ (List.mem_range.mp hp)) (Nat.le_of_lt_succ (List.mem_range.mp ha))

/-- The actual all-core H sends the full synthesis block into itself. The
source and output identities contain no matrix positivity or H-action premise. -/
theorem canonicalPairHamiltonian9_block_mem (d : ℕ) (hd : d < 9)
    (occ : B → (Fin 9 →₀ ℕ)) (words : B → List ℕ)
    (hsource : ∀ b, scaledWord pairFactorialRoot9 ((words b).map fin9) =
      canonicalMonomial (factorialScale 8) (occ b))
    (hlen : ∀ b, (words b).length = 3) (hsum : ∀ b, (words b).sum = d)
    (hmem : ∀ p : Fin (d+1), ∀ a : Fin (p.val+1),
      ∃ b, wordOccupation (pairOutputWord9 d p.val a.val) = occ b)
    (x : B → ℂ) :
    canonicalPairHamiltonian9 d (canonicalBlock (factorialScale 8) occ x) ∈
      canonicalOccupationSpan occ := by
  simp only [canonicalBlock, map_sum, map_smul]
  apply Submodule.sum_mem
  intro b hb
  apply Submodule.smul_mem
  rw [← hsource b]
  exact canonicalPairHamiltonian9_word_mem d hd occ hmem (words b)
    (sourceLabelsBounded9_of_sum_lt _ (by rw [hsum b]; exact hd)) (hlen b) (hsum b)

/-- Orthogonal nonunit canonical monomials reconstruct their actual span with
the inverse original factorial Gram weight, not an assumed isometry. -/
theorem canonicalOccupationSpan_reconstruct (occ : B → (Fin 9 →₀ ℕ))
    (hocc : Function.Injective occ) (f : Core (Fin 9) ℂ) (hf : f ∈ canonicalOccupationSpan occ) :
    canonicalBlock (factorialScale 8) occ (fun b =>
      (occupationMetricWeight (factorialScale 8) (occ b) : ℂ)⁻¹ *
        ip (canonicalMonomial (factorialScale 8) (occ b)) f) = f := by
  have hweight (b : B) : (occupationMetricWeight (factorialScale 8) (occ b) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt
      (occupationMetricWeight_pos (factorialScale 8) (factorialScale_pos 8) _))
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨b,rfl⟩ := hf
    simp [canonicalBlock, canonicalMonomial_inner, hocc.eq_iff, hweight]
  | zero => simp [canonicalBlock, ip, occupationInner_zero_right]
  | add f g hf hg ihf ihg =>
    simpa only [canonicalBlock, ip, occupationInner_add_right, mul_add,
      add_smul, Finset.sum_add_distrib] using congrArg₂ (·+·) ihf ihg
  | smul c f hf ih =>
    simpa only [canonicalBlock, ip, occupationInner_smul_right, Finset.smul_sum,
      smul_smul, mul_left_comm] using congrArg (fun z => c • z) ih

/-- Actual H form, defined from its proven differential action. -/
def actualPairBlockForm (d : ℕ) (occ : B → (Fin 9 →₀ ℕ)) : Matrix B B ℂ :=
  fun a b => ip (canonicalMonomial (factorialScale 8) (occ a))
    (canonicalPairHamiltonian9 d (canonicalMonomial (factorialScale 8) (occ b)))

def canonicalFullInverseGram (occ : B → (Fin 9 →₀ ℕ)) : Matrix B B ℂ :=
  Matrix.diagonal (fun b => (occupationMetricWeight (factorialScale 8) (occ b) : ℂ)⁻¹)

theorem actualPairBlockForm_pair_forms (d : ℕ) (occ : B → (Fin 9 →₀ ℕ)) (a b : B) :
    actualPairBlockForm d occ a b =
      ((List.range (d+1)).map fun p => ((p.factorial : ℂ) / (2 : ℂ)^(p+1)) *
        ip (canonicalPair9 p (canonicalMonomial (factorialScale 8) (occ a)))
          (canonicalPair9 p (canonicalMonomial (factorialScale 8) (occ b)))).sum :=
  canonicalPairHamiltonian9_form d _ _

theorem actualPairBlock_analysis (d : ℕ) (occ : B → (Fin 9 →₀ ℕ)) (x : B → ℂ) (a : B) :
    ip (canonicalMonomial (factorialScale 8) (occ a))
      (canonicalPairHamiltonian9 d (canonicalBlock (factorialScale 8) occ x)) =
      (actualPairBlockForm d occ *ᵥ x) a := by
  simp only [canonicalBlock, map_sum, map_smul, inner_sum_right,
    TwoBodyLift.inner_smul_right, actualPairBlockForm, Matrix.mulVec, dotProduct, mul_comm]

theorem actualPairBlock_cross_form (d : ℕ) (occ : B → (Fin 9 →₀ ℕ)) (x y : B → ℂ) :
    ip (canonicalBlock (factorialScale 8) occ x)
      (canonicalPairHamiltonian9 d (canonicalBlock (factorialScale 8) occ y)) =
      star x ⬝ᵥ (actualPairBlockForm d occ *ᵥ y) := by
  change ip (∑ a, x a • canonicalMonomial (factorialScale 8) (occ a))
    (canonicalPairHamiltonian9 d (canonicalBlock (factorialScale 8) occ y)) = _
  rw [inner_sum_left]
  simp only [TwoBodyLift.inner_smul_left, actualPairBlock_analysis, dotProduct, Pi.star_apply]

theorem canonicalPairHamiltonian9_block_action (d : ℕ) (hd : d < 9)
    (occ : B → (Fin 9 →₀ ℕ)) (hocc : Function.Injective occ) (words : B → List ℕ)
    (hsource : ∀ b, scaledWord pairFactorialRoot9 ((words b).map fin9) =
      canonicalMonomial (factorialScale 8) (occ b))
    (hlen : ∀ b, (words b).length = 3) (hsum : ∀ b, (words b).sum = d)
    (hmem : ∀ p : Fin (d+1), ∀ a : Fin (p.val+1),
      ∃ b, wordOccupation (pairOutputWord9 d p.val a.val) = occ b) (x : B → ℂ) :
    canonicalPairHamiltonian9 d (canonicalBlock (factorialScale 8) occ x) =
      canonicalBlock (factorialScale 8) occ
        ((canonicalFullInverseGram occ * actualPairBlockForm d occ) *ᵥ x) := by
  have h := canonicalOccupationSpan_reconstruct occ hocc
    (canonicalPairHamiltonian9 d (canonicalBlock (factorialScale 8) occ x))
    (canonicalPairHamiltonian9_block_mem d hd occ words hsource hlen hsum hmem x)
  rw [← h]
  congr 1
  funext a
  rw [actualPairBlock_analysis, ← Matrix.mulVec_mulVec]
  simp only [canonicalFullInverseGram, Matrix.mulVec_diagonal]

/-- This is H composed with itself, not the square of a substitute compressed
operator. The middle inverse Gram is justified by true block invariance. -/
theorem canonicalPairHamiltonian9_block_square (d : ℕ) (hd : d < 9)
    (occ : B → (Fin 9 →₀ ℕ)) (hocc : Function.Injective occ) (words : B → List ℕ)
    (hsource : ∀ b, scaledWord pairFactorialRoot9 ((words b).map fin9) =
      canonicalMonomial (factorialScale 8) (occ b))
    (hlen : ∀ b, (words b).length = 3) (hsum : ∀ b, (words b).sum = d)
    (hmem : ∀ p : Fin (d+1), ∀ a : Fin (p.val+1),
      ∃ b, wordOccupation (pairOutputWord9 d p.val a.val) = occ b) (x y : B → ℂ) :
    ip (canonicalBlock (factorialScale 8) occ x)
      (canonicalPairHamiltonian9 d
        (canonicalPairHamiltonian9 d (canonicalBlock (factorialScale 8) occ y))) =
      star x ⬝ᵥ ((actualPairBlockForm d occ * canonicalFullInverseGram occ *
        actualPairBlockForm d occ) *ᵥ y) := by
  rw [canonicalPairHamiltonian9_block_action d hd occ hocc words hsource hlen hsum hmem y]
  rw [actualPairBlock_cross_form, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- The same actual H_8 acts on each degree block: removing any larger pair
weighted degree is genuinely zero, rather than truncated by compression. -/
theorem canonicalPairHamiltonian9_cutoff_block (d e : ℕ) (hde : d ≤ e) (he : e < 9)
    (occ : B → (Fin 9 →₀ ℕ)) (words : B → List ℕ)
    (hsource : ∀ b, scaledWord pairFactorialRoot9 ((words b).map fin9) =
      canonicalMonomial (factorialScale 8) (occ b))
    (hlen : ∀ b, (words b).length = 3) (hsum : ∀ b, (words b).sum = d) (x : B → ℂ) :
    canonicalPairHamiltonian9 e (canonicalBlock (factorialScale 8) occ x) =
      canonicalPairHamiltonian9 d (canonicalBlock (factorialScale 8) occ x) := by
  simp only [canonicalBlock, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← hsource b, canonicalPairHamiltonian9_cutoff_word d e hde he (words b)
    (sourceLabelsBounded9_of_sum_lt _ (by rw [hsum b]; omega)) (hlen b) (hsum b)]

theorem canonicalPairHamiltonian9_H8_block_square (d : ℕ) (hd : d < 9)
    (occ : B → (Fin 9 →₀ ℕ)) (hocc : Function.Injective occ) (words : B → List ℕ)
    (hsource : ∀ b, scaledWord pairFactorialRoot9 ((words b).map fin9) =
      canonicalMonomial (factorialScale 8) (occ b))
    (hlen : ∀ b, (words b).length = 3) (hsum : ∀ b, (words b).sum = d)
    (hmem : ∀ p : Fin (d+1), ∀ a : Fin (p.val+1),
      ∃ b, wordOccupation (pairOutputWord9 d p.val a.val) = occ b) (x y : B → ℂ) :
    ip (canonicalBlock (factorialScale 8) occ x)
      (canonicalPairHamiltonian9 8
        (canonicalPairHamiltonian9 8 (canonicalBlock (factorialScale 8) occ y))) =
      star x ⬝ᵥ ((actualPairBlockForm d occ * canonicalFullInverseGram occ *
        actualPairBlockForm d occ) *ᵥ y) := by
  have hc (z : B → ℂ) := canonicalPairHamiltonian9_cutoff_block d 8 (by omega) (by decide)
    occ words hsource hlen hsum z
  rw [hc y]
  calc
    _ = ip (canonicalBlock (factorialScale 8) occ x)
        (canonicalPairHamiltonian9 d
          (canonicalPairHamiltonian9 d (canonicalBlock (factorialScale 8) occ y))) := by
      rw [canonicalPairHamiltonian9_block_action d hd occ hocc words hsource hlen hsum hmem y, hc]
    _ = _ := canonicalPairHamiltonian9_block_square d hd occ hocc words hsource hlen hsum hmem x y

end Block
end TorusLean.Shared.BosonFiniteCertificateCanonicalPairInvariant
