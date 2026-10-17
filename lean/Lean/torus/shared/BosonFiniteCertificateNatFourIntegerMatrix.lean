import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import Mathlib.Algebra.BigOperators.Field

/-! Exact common-denominator matrix arithmetic certificates. Integer products
are only checked arithmetic witnesses for separately defined rational matrices;
no source operator or comparison is defined by these witnesses. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
namespace TorusLean.BosonFiniteCertificate
open Matrix
open scoped BigOperators

def natFourIntegerMatrix {m n : ℕ} (den : ℕ) (A : Matrix (Fin m) (Fin n) ℤ) :
    Matrix (Fin m) (Fin n) ℚ := fun a b => (A a b : ℚ)/(den : ℚ)

def natFourIntegerEntryCheck {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℤ) : Bool :=
  (List.finRange m).all fun a =>
    (List.finRange n).all fun b => decide (A a b=B a b)

theorem natFourIntegerEntryCheck_sound {m n : ℕ}
    (A B : Matrix (Fin m) (Fin n) ℤ) (h : natFourIntegerEntryCheck A B=true) :
    A=B := by
  funext a b
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp h a (List.mem_finRange a)) b (List.mem_finRange b))

theorem natFourIntegerMatrix_transpose {m n : ℕ}
    (den : ℕ) (A : Matrix (Fin m) (Fin n) ℤ) :
    natFourIntegerMatrix den Aᵀ=(natFourIntegerMatrix den A)ᵀ := rfl

theorem natFourIntegerMatrix_mul {m n k : ℕ} (d e : ℕ)
    (A : Matrix (Fin m) (Fin n) ℤ) (B : Matrix (Fin n) (Fin k) ℤ) :
    natFourIntegerMatrix d A*natFourIntegerMatrix e B=
      natFourIntegerMatrix (d*e) (A*B) := by
  ext a b
  simp only [natFourIntegerMatrix,Matrix.mul_apply,Int.cast_sum,Int.cast_mul,Nat.cast_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  exact div_mul_div_comm _ _ _ _

theorem natFourIntegerMatrix_compression_check {m n : ℕ} (d e : ℕ)
    (A : Matrix (Fin m) (Fin m) ℤ) (W : Matrix (Fin m) (Fin n) ℤ)
    (Y : Matrix (Fin n) (Fin n) ℤ)
    (M : Matrix (Fin m) (Fin m) ℚ) (D : Matrix (Fin m) (Fin n) ℚ)
    (F : Matrix (Fin n) (Fin n) ℚ)
    (hM : natFourIntegerMatrix d A=M) (hD : natFourIntegerMatrix e W=D)
    (hY : Wᵀ*A*W=Y) (hF : natFourIntegerMatrix (e*d*e) Y=F) : Dᵀ*M*D=F := by
  rw [←hD,←hM,←natFourIntegerMatrix_transpose,natFourIntegerMatrix_mul,
    natFourIntegerMatrix_mul,hY,hF]

theorem natFourIntegerMatrix_compression_check_staged {m n : ℕ} (d e : ℕ)
    (A : Matrix (Fin m) (Fin m) ℤ) (W : Matrix (Fin m) (Fin n) ℤ)
    (V : Matrix (Fin n) (Fin m) ℤ) (Y : Matrix (Fin n) (Fin n) ℤ)
    (M : Matrix (Fin m) (Fin m) ℚ) (D : Matrix (Fin m) (Fin n) ℚ)
    (F : Matrix (Fin n) (Fin n) ℚ)
    (hM : natFourIntegerMatrix d A=M) (hD : natFourIntegerMatrix e W=D)
    (hV : Wᵀ*A=V) (hY : V*W=Y) (hF : natFourIntegerMatrix (e*d*e) Y=F) : Dᵀ*M*D=F :=
  natFourIntegerMatrix_compression_check d e A W Y M D F hM hD
    (by rw [hV,hY]) hF

#print axioms natFourIntegerEntryCheck_sound
#print axioms natFourIntegerMatrix_transpose
#print axioms natFourIntegerMatrix_mul
#print axioms natFourIntegerMatrix_compression_check
#print axioms natFourIntegerMatrix_compression_check_staged
end TorusLean.BosonFiniteCertificate
