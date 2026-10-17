import torus.shared.BosonFiniteCertificateCanonicalRowCore
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open Matrix
open scoped BigOperators ComplexConjugate
open TorusLean.M2
open TorusLean.Boson TorusLean.Boson.SpectatorControl TorusLean.Boson.TwoBodyLift
open TorusLean.Shared.BosonFiniteCertificateConjugation
open TorusLean.Shared.BosonFiniteCertificateCoordinate

theorem threeRowAction_singleton (t : ℕ) (c : ℤ) (s : List ℕ) :
    threeRowAction t [c] s = c * (pairRemoval s t : ℤ) := by
  simp [threeRowAction, columns]

/-- The original row square, minus precisely its pure two-body row square.
Every term is an inner product of outputs of actual canonical differential
operators. There is no matrix-defined operator in this definition. -/
def canonicalRowChannel {n r : ℕ} (occ : Fin n → (Fin 9 →₀ ℕ))
    (rows : Fin r → List ℤ) (t : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b => ∑ i,
    (ip (canonicalFrozenRow9 t (rows i) (canonicalMonomial (factorialScale 8) (occ a)))
      (canonicalFrozenRow9 t (rows i) (canonicalMonomial (factorialScale 8) (occ b))) -
    ip (canonicalFrozenRow9 t [rowInteger (rows i) 0]
        (canonicalMonomial (factorialScale 8) (occ a)))
      (canonicalFrozenRow9 t [rowInteger (rows i) 0]
        (canonicalMonomial (factorialScale 8) (occ b))))

theorem complexify_integerForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) :
    complexify (integerForm A) = fun a b => (A a b : ℂ) / 1000000000000000000000000 := by
  ext a b
  simp [complexify, integerForm]

theorem integerForm_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℤ) :
    integerForm (A+B) = integerForm A + integerForm B := by
  ext a b
  simp [integerForm, add_div]

theorem complexify_add_rect {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℚ) :
    complexify (A+B) = complexify A + complexify B := by
  ext a b
  simp [complexify]

/-- Basis-action identities determine the true anchored channel form. The
hypotheses are discharged by the already checked original-word conjugation,
not by assuming the desired matrix positivity or matrix equality. -/
theorem canonicalRowChannel_eq {n r : ℕ} (occ : Fin n → (Fin 9 →₀ ℕ))
    (rows : Fin r → List ℤ) (t q : ℕ) (hq : q < 9)
    (A P : Matrix (Fin r) (Fin n) ℤ)
    (hA : ∀ i a, canonicalFrozenRow9 t (rows i)
      (canonicalMonomial (factorialScale 8) (occ a)) =
        ((A i a : ℂ) / 1000000000000) •
          canonicalMonomial (factorialScale 8) (Finsupp.single (fin9 q) 1))
    (hP : ∀ i a, canonicalFrozenRow9 t [rowInteger (rows i) 0]
      (canonicalMonomial (factorialScale 8) (occ a)) =
        ((P i a : ℂ) / 1000000000000) •
          canonicalMonomial (factorialScale 8) (Finsupp.single (fin9 q) 1)) :
    canonicalRowChannel occ rows t =
      complexify (integerForm ((q.factorial : ℤ) • (Aᵀ * A - Pᵀ * P))) := by
  rw [complexify_integerForm]
  ext a b
  simp only [canonicalRowChannel, Matrix.smul_apply, smul_eq_mul,
    Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Int.cast_mul, Int.cast_natCast, Int.cast_sub, Int.cast_sum]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  rw [hA i a, hA i b, hP i a, hP i b]
  simp only [TwoBodyLift.inner_smul_left, TwoBodyLift.inner_smul_right,
    canonicalMonomial_inner, ite_true, factorial_output_metric q hq]
  simp only [star_div₀, star_intCast, star_ofNat]
  ring

#print axioms canonicalRowChannel_eq
end TorusLean.BosonFiniteCertificate
