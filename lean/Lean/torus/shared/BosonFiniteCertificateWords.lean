import torus.boson.FiniteOccupationCCR
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Count

/-!
# Exact list-word polynomial actions for the rational bosonic certificate

The frozen arithmetic enumerates occupation monomials by lists. This file
proves that its `count`/`erase` recursion is the action of genuine polynomial
partial derivatives, including repeated labels and missing annihilators.
There is no occupation cutoff and the labels may be natural numbers.
-/
set_option autoImplicit false
noncomputable section
namespace TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Boson

variable {ι K : Type*} [DecidableEq ι] [CommRing K]

/-- The actual product of creation variables represented by a label list. -/
def wordPolynomial (s : List ι) : Core ι K := (s.map MvPolynomial.X).prod

theorem wordPolynomial_nil : wordPolynomial ([] : List ι) = (1 : Core ι K) := rfl

theorem wordPolynomial_cons (j : ι) (s : List ι) :
    wordPolynomial (j :: s) = (MvPolynomial.X j : Core ι K) * wordPolynomial s := rfl

theorem wordPolynomial_erase (s : List ι) (j : ι) (hj : j ∈ s) :
    (MvPolynomial.X j : Core ι K) * wordPolynomial (s.erase j) = wordPolynomial s := by
  exact List.prod_map_erase (fun a => (MvPolynomial.X a : Core ι K)) hj

/-- One true derivative gives precisely the falling-factorial first step. -/
theorem pderiv_wordPolynomial (s : List ι) (j : ι) :
    MvPolynomial.pderiv j (wordPolynomial s : Core ι K) =
      s.count j • wordPolynomial (s.erase j) := by
  induction s with
  | nil => simp [wordPolynomial]
  | cons a s ih =>
    by_cases ha : a = j
    · subst a
      rw [wordPolynomial_cons, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_self,
        one_mul, ih]
      by_cases hj : j ∈ s
      · have he := wordPolynomial_erase (K := K) s j hj
        simp only [List.count_cons_self, List.erase_cons_head, add_nsmul, one_nsmul]
        rw [mul_smul_comm, he]
        exact add_comm _ _
      · simp [List.count_eq_zero.mpr hj]
    · simp [wordPolynomial_cons, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X_of_ne ha,
        ih, ha, mul_left_comm]

/-- The finitely supported occupation vector represented by the same list. -/
def wordOccupation : List ι → (ι →₀ ℕ)
  | [] => 0
  | j :: s => Finsupp.single j 1 + wordOccupation s

theorem wordOccupation_apply (s : List ι) (j : ι) :
    wordOccupation s j = s.count j := by
  induction s with
  | nil => simp [wordOccupation]
  | cons a s ih =>
    by_cases h : a = j
    · subst a
      simp [wordOccupation, ih, Nat.add_comm]
    · simp [wordOccupation, Finsupp.add_apply, Finsupp.single_apply, ih, h, Ne.symm h]

/-- The list model and the `MvPolynomial.monomial` coordinate model coincide. -/
theorem wordPolynomial_eq_monomial (s : List ι) :
    (wordPolynomial s : Core ι K) = MvPolynomial.monomial (wordOccupation s) 1 := by
  induction s with
  | nil => simp [wordPolynomial, wordOccupation]
  | cons j s ih =>
    rw [wordPolynomial_cons, ih]
    simp only [MvPolynomial.X, MvPolynomial.monomial_mul_monomial, one_mul, wordOccupation]

/-- The same count-and-erase arithmetic used by the certificate implementation. -/
def wordRemovalWeight : List ι → List ι → ℕ
  | _, [] => 1
  | s, j :: js => s.count j * wordRemovalWeight (s.erase j) js

/-- Labels that remain after the ordered annihilation word. -/
def eraseWord : List ι → List ι → List ι
  | s, [] => s
  | s, j :: js => eraseWord (s.erase j) js

/-- The actual ordered derivative map; the leftmost label acts first. -/
def annihilateWord : List ι → (Core ι K →ₗ[K] Core ι K)
  | [] => LinearMap.id
  | j :: js => (annihilateWord js).comp (annihilate j)

/-- Exact derivative-word semantics, including a zero result for any unavailable
annihilator and the full falling factorial for repeated labels. -/
theorem annihilateWord_wordPolynomial (s labels : List ι) :
    annihilateWord labels (wordPolynomial s : Core ι K) =
      wordRemovalWeight s labels • wordPolynomial (eraseWord s labels) := by
  induction labels generalizing s with
  | nil => simp [annihilateWord, wordRemovalWeight, eraseWord]
  | cons j js ih =>
    change annihilateWord js (annihilate j (wordPolynomial s : Core ι K)) = _
    rw [show annihilate j (wordPolynomial s : Core ι K) =
      s.count j • wordPolynomial (s.erase j) from pderiv_wordPolynomial s j]
    rw [map_nsmul, ih, smul_smul]
    rfl

/-- The same identity with a field/ring coefficient, matching rational matrix entries. -/
theorem annihilateWord_wordPolynomial_cast (s labels : List ι) :
    annihilateWord labels (wordPolynomial s : Core ι K) =
      (wordRemovalWeight s labels : K) • wordPolynomial (eraseWord s labels) := by
  simpa only [Nat.cast_smul_eq_nsmul] using
    annihilateWord_wordPolynomial (K := K) s labels

/-- Creators are actual multiplication by the requested output word. -/
def normalWord (creators annihilators : List ι) : Core ι K →ₗ[K] Core ι K :=
  (LinearMap.mulLeft K (wordPolynomial creators)).comp (annihilateWord annihilators)

theorem normalWord_wordPolynomial (s creators annihilators : List ι) :
    normalWord creators annihilators (wordPolynomial s : Core ι K) =
      (wordRemovalWeight s annihilators : K) •
        wordPolynomial (creators ++ eraseWord s annihilators) := by
  change wordPolynomial creators * annihilateWord annihilators (wordPolynomial s : Core ι K) = _
  rw [annihilateWord_wordPolynomial_cast, mul_smul_comm]
  simp only [wordPolynomial, List.map_append, List.prod_append]

#print axioms wordOccupation_apply
#print axioms wordPolynomial_eq_monomial
#print axioms pderiv_wordPolynomial
#print axioms annihilateWord_wordPolynomial
#print axioms annihilateWord_wordPolynomial_cast
#print axioms normalWord_wordPolynomial

end TorusLean.Shared.BosonFiniteCertificateWords
