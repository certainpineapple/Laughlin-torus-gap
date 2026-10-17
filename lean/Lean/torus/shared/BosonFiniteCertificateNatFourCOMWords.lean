import torus.shared.BosonFiniteCertificateNatFourBasisCore
import torus.shared.BosonFiniteCertificateNatCOMLower

/-! Whole-core Nat COM lowering in the original factorial coordinates.
The source is a genuine polynomial derivation. Finite lower matrices will be
identified with this operator only after independent word-action checks. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
noncomputable section
namespace TorusLean.BosonFiniteCertificate
open TorusLean.Boson
open TorusLean.Shared.BosonFiniteCertificateWords
open TorusLean.Shared.BosonFiniteCertificateConjugation
open Matrix
open scoped BigOperators

def paperNatFourCOMLower : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ :=
  (MvPolynomial.mkDerivation ℂ (fun j : ℕ =>
    (j : ℂ) • (MvPolynomial.X (j-1) : Core ℕ ℂ))).toLinearMap

theorem paperNatFourCOMLower_X (j : ℕ) :
    paperNatFourCOMLower (MvPolynomial.X j) = (j : ℂ) • MvPolynomial.X (j-1) :=
  MvPolynomial.mkDerivation_X ℂ _ j

theorem paperNatFourCOMLower_C (c : ℂ) :
    paperNatFourCOMLower (MvPolynomial.C c) = 0 := MvPolynomial.derivation_C _ c

theorem paperNatFourCOMLower_mul (p q : Core ℕ ℂ) :
    paperNatFourCOMLower (p*q) = paperNatFourCOMLower p*q+p*paperNatFourCOMLower q := by
  simpa only [paperNatFourCOMLower,Derivation.coeFn_coe,smul_eq_mul,mul_comm,add_comm] using
    (MvPolynomial.mkDerivation ℂ (fun j : ℕ =>
      (j : ℂ) • (MvPolynomial.X (j-1) : Core ℕ ℂ))).leibniz p q

theorem natFour_factorialRoot_lower (j : ℕ) :
    factorialRootNat j * (Real.sqrt (j : ℝ) : ℂ) =
      (j : ℂ) * factorialRootNat (j-1) := by
  cases j with
  | zero => simp
  | succ j =>
    rw [factorialRootNat_succ]
    have h : (Real.sqrt (j+1 : ℝ) : ℂ) * (Real.sqrt (j+1 : ℝ) : ℂ) = (j+1 : ℂ) := by
      exact_mod_cast Real.mul_self_sqrt (show (0 : ℝ) ≤ j+1 by positivity)
    have hc : (Real.sqrt ((j+1 : ℕ) : ℝ) : ℂ) = (Real.sqrt (j+1 : ℝ) : ℂ) := by norm_cast
    simp only [Nat.succ_sub_one,Nat.cast_add,Nat.cast_one,hc]
    calc
      _ = ((Real.sqrt (j+1 : ℝ) : ℂ) * (Real.sqrt (j+1 : ℝ) : ℂ)) * factorialRootNat j := by ring
      _ = _ := by rw [h]

/-- True unbounded lowering commutes with the invertible factorial change of
variables, on every polynomial. This is not a cutoff definition. -/
theorem canonicalNatFourCOMLower_rescale (p : Core ℕ ℂ) :
    canonicalCOMLowerNat (rescaleHom factorialRootNat p) =
      rescaleHom factorialRootNat (paperNatFourCOMLower p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp only [rescaleHom,MvPolynomial.aeval_C,MvPolynomial.algebraMap_eq,
      paperNatFourCOMLower_C,canonicalCOMLowerNat_C,map_zero]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p j hp =>
    rw [map_mul,canonicalCOMLowerNat_mul,hp,paperNatFourCOMLower_mul,map_add,map_mul,map_mul,
      paperNatFourCOMLower_X,rescaleHom_X]
    simp only [map_smul,rescaleHom_X,canonicalCOMLowerNat_X,smul_smul,natFour_factorialRoot_lower]

theorem canonicalNatFourCOMLower_conjugate :
    conjugateOperator factorialRootNat factorialRootNat_ne_zero paperNatFourCOMLower =
      canonicalCOMLowerNat := by
  apply LinearMap.ext
  intro f
  obtain ⟨p,rfl⟩ := (rescaleEquiv factorialRootNat factorialRootNat_ne_zero).surjective f
  rw [conjugateOperator_apply_rescale]
  exact (canonicalNatFourCOMLower_rescale p).symm

/-- Positional lowering, retaining all repeated particle positions. A zero
orbital contributes its exact zero coefficient. -/
def natFourLoweredWords : List ℕ → List (ℕ × List ℕ)
  | [] => []
  | j :: s => (j,(j-1)::s) ::
      (natFourLoweredWords s).map (fun cw => (cw.1,j::cw.2))

theorem paperNatFourCOMLower_word (s : List ℕ) :
    paperNatFourCOMLower (wordPolynomial s) =
      ((natFourLoweredWords s).map fun cw =>
        (cw.1 : ℂ) • (wordPolynomial cw.2 : Core ℕ ℂ)).sum := by
  induction s with
  | nil => simpa only [wordPolynomial_nil,natFourLoweredWords,List.map_nil,List.sum_nil,map_one] using
      paperNatFourCOMLower_C 1
  | cons j s ih =>
    rw [wordPolynomial_cons,paperNatFourCOMLower_mul,paperNatFourCOMLower_X,ih]
    simp only [natFourLoweredWords,List.map_cons,List.sum_cons,List.map_map,Function.comp_def,
      wordPolynomial_cons,smul_mul_assoc]
    rw [← List.sum_map_mul_left]
    simp only [mul_smul_comm]

theorem canonicalNatFourCOMLower_scaledWord (s : List ℕ) :
    canonicalCOMLowerNat (scaledWord factorialRootNat s) =
      ((natFourLoweredWords s).map fun cw =>
        (cw.1 : ℂ) • scaledWord factorialRootNat cw.2).sum := by
  rw [← rescaleHom_word,canonicalNatFourCOMLower_rescale,paperNatFourCOMLower_word,
    map_list_sum,List.map_map]
  simp only [Function.comp_def,map_smul,rescaleHom_word]

/-- Rectangular synthesis after a real source action has been established on
each basis word. The matrix is an input to an equality proof, not an operator
definition. -/
theorem natFourWordBlock_rect_action {m n : ℕ}
    (src : Fin n → List ℕ) (dst : Fin m → List ℕ)
    (A : Core ℕ ℂ →ₗ[ℂ] Core ℕ ℂ) (M : Matrix (Fin m) (Fin n) ℂ)
    (hA : ∀ a, A (scaledWord factorialRootNat (src a)) =
      ∑ b, M b a • scaledWord factorialRootNat (dst b)) (x : Fin n → ℂ) :
    A (natFourWordBlock src x) = natFourWordBlock dst (M *ᵥ x) := by
  simp only [natFourWordBlock,map_sum,map_smul,hA,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  simp only [Matrix.mulVec,dotProduct,Finset.sum_smul,mul_comm]

#print axioms paperNatFourCOMLower_X
#print axioms paperNatFourCOMLower_C
#print axioms paperNatFourCOMLower_mul
#print axioms natFour_factorialRoot_lower
#print axioms canonicalNatFourCOMLower_rescale
#print axioms canonicalNatFourCOMLower_conjugate
#print axioms paperNatFourCOMLower_word
#print axioms canonicalNatFourCOMLower_scaledWord
#print axioms natFourWordBlock_rect_action
end TorusLean.BosonFiniteCertificate
