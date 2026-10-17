import torus.shared.BosonFiniteCertificateConjugation
import Mathlib.Algebra.BigOperators.Ring.List

/-! Genuine locally finite COM raising on all natural orbital labels. The
operator is an actual polynomial derivation, not the top-truncated Fin9
operator. All sums in its monomial action are finite by polynomial support. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation

def factorialRootNat (j : ℕ) : ℂ := (Real.sqrt (j.factorial : ℝ) : ℂ)

theorem factorialRootNat_ne_zero (j : ℕ) : factorialRootNat j ≠ 0 := by
  unfold factorialRootNat
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr
    (Nat.cast_pos.mpr (Nat.factorial_pos j))))

def paperCOMRaiseNat : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  (MvPolynomial.mkDerivation ℂ (fun j : ℕ => (MvPolynomial.X (j+1) : Core ℕ ℂ))).toLinearMap

def canonicalCOMRaiseNat : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  (MvPolynomial.mkDerivation ℂ (fun j : ℕ =>
    (Real.sqrt (j+1 : ℝ) : ℂ) • (MvPolynomial.X (j+1) : Core ℕ ℂ))).toLinearMap

theorem paperCOMRaiseNat_X (j : ℕ) :
    paperCOMRaiseNat (MvPolynomial.X j) = MvPolynomial.X (j+1) :=
  MvPolynomial.mkDerivation_X ℂ _ j

theorem canonicalCOMRaiseNat_X (j : ℕ) :
    canonicalCOMRaiseNat (MvPolynomial.X j) =
      (Real.sqrt (j+1 : ℝ) : ℂ) • MvPolynomial.X (j+1) :=
  MvPolynomial.mkDerivation_X ℂ _ j

theorem paperCOMRaiseNat_C (c : ℂ) : paperCOMRaiseNat (MvPolynomial.C c) = 0 :=
  MvPolynomial.derivation_C _ c

theorem canonicalCOMRaiseNat_C (c : ℂ) : canonicalCOMRaiseNat (MvPolynomial.C c) = 0 :=
  MvPolynomial.derivation_C _ c

theorem paperCOMRaiseNat_mul (p q : Core ℕ ℂ) :
    paperCOMRaiseNat (p*q) = paperCOMRaiseNat p*q + p*paperCOMRaiseNat q := by
  simpa only [paperCOMRaiseNat, Derivation.coeFn_coe, smul_eq_mul, mul_comm, add_comm] using
    (MvPolynomial.mkDerivation ℂ (fun j : ℕ => (MvPolynomial.X (j+1) : Core ℕ ℂ))).leibniz p q

theorem canonicalCOMRaiseNat_mul (p q : Core ℕ ℂ) :
    canonicalCOMRaiseNat (p*q) = canonicalCOMRaiseNat p*q + p*canonicalCOMRaiseNat q := by
  simpa only [canonicalCOMRaiseNat, Derivation.coeFn_coe, smul_eq_mul, mul_comm, add_comm] using
    (MvPolynomial.mkDerivation ℂ (fun j : ℕ =>
      (Real.sqrt (j+1 : ℝ) : ℂ) • (MvPolynomial.X (j+1) : Core ℕ ℂ))).leibniz p q

theorem factorialRootNat_succ (j : ℕ) :
    factorialRootNat (j+1) = (Real.sqrt (j+1 : ℝ) : ℂ) * factorialRootNat j := by
  unfold factorialRootNat
  rw [Nat.factorial_succ,Nat.cast_mul,Real.sqrt_mul (by positivity),Complex.ofReal_mul]
  norm_cast

/-- The original paper-variable raising and canonical raising are related by
the actual invertible sqrt-factorial algebra substitution on the entire core. -/
theorem canonicalCOMRaiseNat_rescale (p : Core ℕ ℂ) :
    canonicalCOMRaiseNat (rescaleHom factorialRootNat p) =
      rescaleHom factorialRootNat (paperCOMRaiseNat p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp only [rescaleHom,MvPolynomial.aeval_C,MvPolynomial.algebraMap_eq,paperCOMRaiseNat_C,canonicalCOMRaiseNat_C,map_zero]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p j hp =>
    rw [map_mul,canonicalCOMRaiseNat_mul,hp,paperCOMRaiseNat_mul,map_add,map_mul,map_mul,
      paperCOMRaiseNat_X,rescaleHom_X,rescaleHom_X,map_smul,canonicalCOMRaiseNat_X,
      factorialRootNat_succ]
    simp only [smul_smul, mul_comm]

theorem canonicalCOMRaiseNat_conjugate :
    conjugateOperator factorialRootNat factorialRootNat_ne_zero paperCOMRaiseNat =
      canonicalCOMRaiseNat := by
  apply LinearMap.ext
  intro f
  obtain ⟨p,rfl⟩ := (rescaleEquiv factorialRootNat factorialRootNat_ne_zero).surjective f
  rw [conjugateOperator_apply_rescale]
  exact (canonicalCOMRaiseNat_rescale p).symm

/-- One word for each raised particle position. Repeated orbital labels are
retained as repeated list entries and therefore retain bosonic multiplicity. -/
def raisedWordsNat : List ℕ → List (List ℕ)
  | [] => []
  | j :: s => ((j+1) :: s) :: (raisedWordsNat s).map (List.cons j)

theorem raisedWordsNat_length (s w : List ℕ) (hw : w ∈ raisedWordsNat s) :
    w.length = s.length := by
  induction s generalizing w with
  | nil => simp [raisedWordsNat] at hw
  | cons j s ih =>
    simp only [raisedWordsNat,List.mem_cons,List.mem_map] at hw
    rcases hw with rfl | ⟨v,hv,rfl⟩
    · rfl
    · simp only [List.length_cons,ih v hv]

theorem raisedWordsNat_sum (s w : List ℕ) (hw : w ∈ raisedWordsNat s) :
    w.sum = s.sum+1 := by
  induction s generalizing w with
  | nil => simp [raisedWordsNat] at hw
  | cons j s ih =>
    simp only [raisedWordsNat,List.mem_cons,List.mem_map] at hw
    rcases hw with rfl | ⟨v,hv,rfl⟩
    · simp only [List.sum_cons]; omega
    · simp only [List.sum_cons,ih v hv]; omega

theorem paperCOMRaiseNat_word (s : List ℕ) :
    paperCOMRaiseNat (wordPolynomial s) =
      ((raisedWordsNat s).map (fun w => (wordPolynomial w : Core ℕ ℂ))).sum := by
  induction s with
  | nil => simpa only [wordPolynomial_nil,raisedWordsNat,List.map_nil,List.sum_nil,map_one] using
      paperCOMRaiseNat_C 1
  | cons j s ih =>
    rw [wordPolynomial_cons,paperCOMRaiseNat_mul,paperCOMRaiseNat_X,ih]
    simp only [raisedWordsNat,List.map_cons,List.sum_cons,List.map_map,Function.comp_def,
      wordPolynomial_cons,List.sum_map_mul_left]

theorem canonicalCOMRaiseNat_scaledWord (s : List ℕ) :
    canonicalCOMRaiseNat (scaledWord factorialRootNat s) =
      ((raisedWordsNat s).map (scaledWord factorialRootNat)).sum := by
  rw [← rescaleHom_word,canonicalCOMRaiseNat_rescale,paperCOMRaiseNat_word,
    map_list_sum,List.map_map]
  simp only [Function.comp_def,rescaleHom_word]

/-- Exact positional raising for an arbitrary true canonical three-word. -/
theorem canonicalCOMRaiseNat_threeWord (a b c : ℕ) :
    canonicalCOMRaiseNat (wordPolynomial [a,b,c]) =
      (Real.sqrt (a+1 : ℝ) : ℂ) • wordPolynomial [a+1,b,c] +
      (Real.sqrt (b+1 : ℝ) : ℂ) • wordPolynomial [a,b+1,c] +
      (Real.sqrt (c+1 : ℝ) : ℂ) • wordPolynomial [a,b,c+1] := by
  have hOne : canonicalCOMRaiseNat 1 = 0 := by simpa using canonicalCOMRaiseNat_C 1
  simp only [wordPolynomial_cons,wordPolynomial_nil,canonicalCOMRaiseNat_mul,
    canonicalCOMRaiseNat_X,hOne,mul_zero,add_zero,mul_one,
    smul_mul_assoc,mul_smul_comm,mul_add,add_assoc]

#print axioms canonicalCOMRaiseNat_conjugate
#print axioms canonicalCOMRaiseNat_scaledWord
#print axioms canonicalCOMRaiseNat_threeWord
#print axioms raisedWordsNat_length
#print axioms raisedWordsNat_sum
end TorusLean.BosonFiniteCertificate
