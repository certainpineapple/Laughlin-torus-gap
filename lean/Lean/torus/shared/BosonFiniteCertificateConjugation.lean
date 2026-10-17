/- Actual invertible change of polynomial variables, before any finite-block
Riesz realization. No Gram inverse or positivity is an assumption. -/
import torus.shared.BosonFiniteCertificateAction
import torus.shared.BosonFiniteCertificateCoordinate
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateAction
open TorusLean.BosonFiniteCertificate

variable {ι K : Type*} [DecidableEq ι] [Field K]

def wordScale (κ : ι → K) (s : List ι) : K := (s.map κ).prod

def scaledWord (κ : ι → K) (s : List ι) : Core ι K :=
  wordScale κ s • wordPolynomial s

/-- The map x_j ↦ κ_j X_j is an actual polynomial algebra homomorphism. -/
def rescaleHom (κ : ι → K) : Core ι K →ₐ[K] Core ι K :=
  MvPolynomial.aeval (fun j => κ j • MvPolynomial.X j)

theorem rescaleHom_X (κ : ι → K) (j : ι) :
    rescaleHom κ (MvPolynomial.X j) = κ j • MvPolynomial.X j := by
  simp [rescaleHom]

/-- The inverse uses 1/κ_j on each variable; no finite-degree truncation. -/
def rescaleEquiv (κ : ι → K) (hκ : ∀ j, κ j ≠ 0) : Core ι K ≃ₐ[K] Core ι K :=
  AlgEquiv.ofAlgHom (rescaleHom κ) (rescaleHom (fun j => (κ j)⁻¹))
    (by
      ext j
      simp [AlgHom.comp_apply, rescaleHom_X, map_smul, smul_smul, hκ])
    (by
      ext j
      simp [AlgHom.comp_apply, rescaleHom_X, map_smul, smul_smul, hκ])

theorem rescaleHom_word (κ : ι → K) (s : List ι) :
    rescaleHom κ (wordPolynomial s) = scaledWord κ s := by
  induction s with
  | nil => simp [wordPolynomial, scaledWord, wordScale]
  | cons j s ih =>
    rw [wordPolynomial_cons, map_mul, rescaleHom_X, ih]
    simp only [scaledWord, wordScale, List.map_cons, List.prod_cons,
      wordPolynomial_cons, smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm]

theorem rescaleEquiv_word (κ : ι → K) (hκ : ∀ j, κ j ≠ 0) (s : List ι) :
    rescaleEquiv κ hκ (wordPolynomial s) = scaledWord κ s :=
  rescaleHom_word κ s

/-- Conjugation of an actual differential operator by the explicit variable
rescaling. It acts on the whole polynomial core, rather than being a zero
extension from a finite relative family. -/
def conjugateOperator (κ : ι → K) (hκ : ∀ j, κ j ≠ 0)
    (A : Core ι K →ₗ[K] Core ι K) : Core ι K →ₗ[K] Core ι K :=
  (rescaleEquiv κ hκ).toLinearEquiv.toLinearMap.comp
    (A.comp (rescaleEquiv κ hκ).symm.toLinearEquiv.toLinearMap)

theorem conjugateOperator_apply_rescale (κ : ι → K) (hκ : ∀ j, κ j ≠ 0)
    (A : Core ι K →ₗ[K] Core ι K) (f : Core ι K) :
    conjugateOperator κ hκ A (rescaleEquiv κ hκ f) = rescaleEquiv κ hκ (A f) := by
  simp [conjugateOperator]

/-- Every genuine normal word is transported on every word input, before any
finite block or Riesz realization. Word inputs span the full polynomial core. -/
theorem conjugated_normalWord_action (κ : ι → K) (hκ : ∀ j, κ j ≠ 0)
    (s creators annihilators : List ι) :
    conjugateOperator κ hκ (normalWord creators annihilators) (scaledWord κ s) =
      (wordRemovalWeight s annihilators : K) •
        scaledWord κ (creators ++ eraseWord s annihilators) := by
  rw [← rescaleEquiv_word κ hκ, conjugateOperator_apply_rescale,
    normalWord_wordPolynomial, map_smul, rescaleEquiv_word]

/-- Rename is a true algebra embedding when orbital labels are injected. -/
theorem rename_wordPolynomial {τ : Type*} [DecidableEq τ]
    (f : ι → τ) (s : List ι) :
    MvPolynomial.rename f (wordPolynomial s : Core ι K) =
      wordPolynomial (s.map f) := by
  induction s with
  | nil => simp [wordPolynomial]
  | cons j s ih =>
    simp only [wordPolynomial_cons, map_mul, MvPolynomial.rename_X,
      List.map_cons, ih]

theorem annihilateWord_rename {τ : Type*} [DecidableEq τ]
    (f : ι → τ) (hf : Function.Injective f) (labels : List ι) (p : Core ι K) :
    annihilateWord (labels.map f) (MvPolynomial.rename f p) =
      MvPolynomial.rename f (annihilateWord labels p) := by
  induction labels generalizing p with
  | nil => simp [annihilateWord]
  | cons j js ih =>
    change annihilateWord (js.map f) (annihilate (f j) (MvPolynomial.rename f p)) =
      MvPolynomial.rename f (annihilateWord js (annihilate j p))
    rw [show annihilate (f j) (MvPolynomial.rename f p) =
      MvPolynomial.rename f (annihilate j p) from MvPolynomial.pderiv_rename hf j p, ih]

/-- Injective relabeling intertwines the genuine creator/derivative word on
all polynomial inputs. No support table is used to define the operator. -/
theorem normalWord_rename {τ : Type*} [DecidableEq τ]
    (f : ι → τ) (hf : Function.Injective f)
    (creators annihilators : List ι) (p : Core ι K) :
    normalWord (creators.map f) (annihilators.map f) (MvPolynomial.rename f p) =
      MvPolynomial.rename f (normalWord creators annihilators p) := by
  change wordPolynomial (creators.map f) *
    annihilateWord (annihilators.map f) (MvPolynomial.rename f p) =
      MvPolynomial.rename f (wordPolynomial creators * annihilateWord annihilators p)
  rw [annihilateWord_rename f hf, ← rename_wordPolynomial, map_mul]

/-- Original frozen row conjugated by x_j ↦ κ_j X_j, with its true output.
The finite output-shape condition has already been checked for all 41 source
three-particle basis words in ActualThree. -/
theorem conjugated_frozen_row_action (κ : ℕ → K) (hκ : ∀ j, κ j ≠ 0)
    (t d : ℕ) (row : List ℤ) (s : List ℕ) (h : rowOutputOK t d s = true) :
    conjugateOperator κ hκ (paperRowWordOperator t row) (scaledWord κ s) =
      ((threeRowAction t row s : K) / 1000000000000) •
        (κ (d-t) • MvPolynomial.X (d-t)) := by
  rw [← rescaleEquiv_word κ hκ, conjugateOperator_apply_rescale,
    paperRowWordOperator_apply t d row s h, map_smul]
  change _ • rescaleHom κ (MvPolynomial.X (d-t)) = _
  rw [rescaleHom_X]

/-- For finite orbital labels, the explicit variable rescaling agrees with
exactly the canonical monomial already used by the three-particle bridge. -/
theorem orbitalWeight_add_single [Fintype ι] [Nonempty ι]
    (scale : ι → ℕ) (j : ι) (n : ι →₀ ℕ) :
    TorusLean.Shared.BosonFiniteCertificateCoordinate.orbitalWeight scale
      (Finsupp.single j 1 + n) = scale j *
      TorusLean.Shared.BosonFiniteCertificateCoordinate.orbitalWeight scale n := by
  classical
  simp only [TorusLean.Shared.BosonFiniteCertificateCoordinate.orbitalWeight,
    Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]
  congr 1
  simp [Finsupp.single_apply, eq_comm]

theorem wordScale_sqrt_occupation [Fintype ι] [Nonempty ι]
    (scale : ι → ℕ) (s : List ι) :
    wordScale (fun j => (Real.sqrt (scale j : ℝ) : ℂ)) s =
      (Real.sqrt (TorusLean.Shared.BosonFiniteCertificateCoordinate.orbitalWeight
        scale (wordOccupation s) : ℝ) : ℂ) := by
  induction s with
  | nil => simp [wordScale, wordOccupation,
      TorusLean.Shared.BosonFiniteCertificateCoordinate.orbitalWeight]
  | cons j s ih =>
    simp only [wordScale, List.map_cons, List.prod_cons] at ih ⊢
    rw [wordOccupation, orbitalWeight_add_single, Nat.cast_mul,
      Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul, ← ih]

theorem scaledWord_eq_canonicalMonomial [Fintype ι] [Nonempty ι]
    (scale : ι → ℕ) (s : List ι) :
    scaledWord (fun j => (Real.sqrt (scale j : ℝ) : ℂ)) s =
      TorusLean.Shared.BosonFiniteCertificateCoordinate.canonicalMonomial
        scale (wordOccupation s) := by
  rw [scaledWord, wordPolynomial_eq_monomial, wordScale_sqrt_occupation]
  simp [TorusLean.Shared.BosonFiniteCertificateCoordinate.canonicalMonomial,
    MvPolynomial.smul_monomial]

#print axioms conjugated_normalWord_action
#print axioms normalWord_rename
#print axioms orbitalWeight_add_single
#print axioms wordScale_sqrt_occupation
#print axioms scaledWord_eq_canonicalMonomial
#print axioms rescaleHom_word
#print axioms rescaleEquiv_word
#print axioms conjugateOperator_apply_rescale
#print axioms conjugated_frozen_row_action
end TorusLean.Shared.BosonFiniteCertificateConjugation
