import torus.shared.BosonFiniteCertificateNatCOM
import torus.shared.BosonFiniteCertificateNatOccupationInner
import torus.shared.BosonFiniteCertificateRescaleCCR

/-!
# All-natural-label normal words and the physical factorial metric

This source defines no matrix-derived operator. Its operators are the genuine
creator / derivative words, conjugated by x_j = sqrt(j!) X_j on the whole
polynomial core. Every list keeps repeated labels. The rational cross-form
below is derived from that action and the genuine occupation inner product.
It does not assume a four-particle cutoff, relative span, or positivity.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.BosonFiniteCertificateRescaleCCR

/-- Orbital factorial product. Multiplicity factorials are supplied separately
by the genuine occupation weight, so repeated orbital labels are not lost. -/
def natFourOrbitalMetric (s : List ℕ) : ℕ := (s.map Nat.factorial).prod

/-- Exactly prod_j n_j! times prod of the orbital factorials. -/
def natFourWordMetric (s : List ℕ) : ℕ :=
  natOccupationWeight (wordOccupation s) * natFourOrbitalMetric s

theorem factorialRootNat_star_mul (j : ℕ) :
    star (factorialRootNat j) * factorialRootNat j = (j.factorial : ℂ) := by
  simp only [factorialRootNat, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul]
  rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]
  rfl

theorem natFour_wordScale_star_mul (s : List ℕ) :
    star (wordScale factorialRootNat s) * wordScale factorialRootNat s =
      (natFourOrbitalMetric s : ℂ) := by
  induction s with
  | nil => simp [wordScale, natFourOrbitalMetric]
  | cons j s ih =>
    simp only [wordScale, List.map_cons, List.prod_cons, star_mul,
      natFourOrbitalMetric, Nat.cast_mul] at ih ⊢
    calc
      star ((s.map factorialRootNat).prod) * star (factorialRootNat j) *
          (factorialRootNat j * (s.map factorialRootNat).prod) =
        (star (factorialRootNat j) * factorialRootNat j) *
          (star ((s.map factorialRootNat).prod) * (s.map factorialRootNat).prod) := by ring
      _ = (j.factorial : ℂ) * ((s.map Nat.factorial).prod : ℂ) := by
        rw [factorialRootNat_star_mul, ih]

theorem natFour_wordScale_eq_of_occupation_eq (s u : List ℕ)
    (h : wordOccupation s = wordOccupation u) :
    wordScale factorialRootNat s = wordScale factorialRootNat u := by
  have hp : s.Perm u := List.perm_iff_count.mpr fun j => by
    simpa only [wordOccupation_apply] using congrArg (fun n : ℕ →₀ ℕ => n j) h
  exact (hp.map factorialRootNat).prod_eq

theorem natFour_scaledWord_monomial (s : List ℕ) :
    scaledWord factorialRootNat s =
      MvPolynomial.monomial (wordOccupation s) (wordScale factorialRootNat s) := by
  simp only [scaledWord, wordPolynomial_eq_monomial, MvPolynomial.smul_monomial,
    smul_eq_mul, mul_one]

/-- Full factorial-metric cross-form, with equality of occupations rather than
list order. In particular no bosonic multiplicity is discarded by sorting. -/
theorem natFour_scaledWord_inner (s u : List ℕ) :
    natOccupationInner (scaledWord factorialRootNat s) (scaledWord factorialRootNat u) =
      if wordOccupation s = wordOccupation u then (natFourWordMetric s : ℂ) else 0 := by
  rw [natFour_scaledWord_monomial, natFour_scaledWord_monomial,
    natOccupationInner_monomial_left, MvPolynomial.coeff_monomial]
  by_cases h : wordOccupation s = wordOccupation u
  · simp only [h, ite_true]
    rw [← h, ← natFour_wordScale_eq_of_occupation_eq s u h,
      mul_assoc, natFour_wordScale_star_mul]
    exact (Nat.cast_mul _ _).symm
  · simp [h, Ne.symm h]

/-- Exact rational cross-form of one true, factorial-conjugated normal word. -/
def natFourNormalWordForm (s u creators annihilators : List ℕ) : ℚ :=
  if wordOccupation s = wordOccupation (creators ++ eraseWord u annihilators) then
    (wordRemovalWeight u annihilators : ℚ) * (natFourWordMetric s : ℚ)
  else 0

def canonicalNatFourNormalWord (creators annihilators : List ℕ) :
    Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  conjugateOperator factorialRootNat factorialRootNat_ne_zero
    (normalWord creators annihilators)

/-- Actual operator action on the unbounded Nat-label polynomial common core. -/
theorem canonicalNatFourNormalWord_action (s creators annihilators : List ℕ) :
    canonicalNatFourNormalWord creators annihilators (scaledWord factorialRootNat s) =
      (wordRemovalWeight s annihilators : ℂ) •
        scaledWord factorialRootNat (creators ++ eraseWord s annihilators) :=
  conjugated_normalWord_action factorialRootNat factorialRootNat_ne_zero s creators annihilators

theorem canonicalNatFourNormalWord_form (s u creators annihilators : List ℕ) :
    natOccupationInner (scaledWord factorialRootNat s)
      (canonicalNatFourNormalWord creators annihilators (scaledWord factorialRootNat u)) =
      (natFourNormalWordForm s u creators annihilators : ℂ) := by
  rw [canonicalNatFourNormalWord_action, natOccupationInner_smul_right,
    natFour_scaledWord_inner]
  by_cases h : wordOccupation s = wordOccupation (creators ++ eraseWord u annihilators)
  · simp [natFourNormalWordForm, h]
  · simp [natFourNormalWordForm, h]

/-- A coefficient tensor entry, not a finite-matrix realization. -/
structure NatFourNormalTerm where
  coefficient : ℚ
  creators : List ℕ
  annihilators : List ℕ

def paperNatFourTerms (terms : List NatFourNormalTerm) : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  (terms.map fun term => (term.coefficient : ℂ) •
    normalWord term.creators term.annihilators).sum

def canonicalNatFourTerms (terms : List NatFourNormalTerm) : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  (terms.map fun term => (term.coefficient : ℂ) •
    canonicalNatFourNormalWord term.creators term.annihilators).sum

def natFourTermsForm (terms : List NatFourNormalTerm) (s u : List ℕ) : ℚ :=
  (terms.map fun term => term.coefficient *
    natFourNormalWordForm s u term.creators term.annihilators).sum

/-- The whole finite normal tensor is conjugated on every polynomial input. -/
theorem canonicalNatFourTerms_conjugate (terms : List NatFourNormalTerm) :
    canonicalNatFourTerms terms =
      conjugateOperator factorialRootNat factorialRootNat_ne_zero (paperNatFourTerms terms) := by
  induction terms with
  | nil =>
    apply LinearMap.ext
    intro f
    simp [canonicalNatFourTerms, paperNatFourTerms, conjugateOperator]
  | cons term terms ih =>
    simp only [canonicalNatFourTerms, paperNatFourTerms, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    apply LinearMap.ext
    intro f
    simp [canonicalNatFourNormalWord, conjugateOperator]

/-- Reusable bridge from original rational normal-word coefficients to the
true unlimited-label occupation form. No candidate matrix is an assumption. -/
theorem canonicalNatFourTerms_form (terms : List NatFourNormalTerm) (s u : List ℕ) :
    natOccupationInner (scaledWord factorialRootNat s)
      (canonicalNatFourTerms terms (scaledWord factorialRootNat u)) =
      (natFourTermsForm terms s u : ℂ) := by
  induction terms with
  | nil => simp [canonicalNatFourTerms, natFourTermsForm, natOccupationInner_zero_right]
  | cons term terms ih =>
    simp only [canonicalNatFourTerms, List.map_cons, List.sum_cons,
      LinearMap.add_apply, LinearMap.smul_apply] at ih ⊢
    rw [natOccupationInner_add_right, natOccupationInner_smul_right,
      canonicalNatFourNormalWord_form, ih]
    simp [natFourTermsForm]

#print axioms factorialRootNat_star_mul
#print axioms natFour_wordScale_star_mul
#print axioms natFour_wordScale_eq_of_occupation_eq
#print axioms natFour_scaledWord_monomial
#print axioms natFour_scaledWord_inner
#print axioms canonicalNatFourNormalWord_action
#print axioms canonicalNatFourNormalWord_form
#print axioms canonicalNatFourTerms_conjugate
#print axioms canonicalNatFourTerms_form
end TorusLean.BosonFiniteCertificate
