import torus.shared.BosonFiniteCertificateNatFourEntryCheck
import Mathlib.Data.List.FinRange

/-! Exact sparse evaluation of an independently fixed dense rational matrix.
Every omitted column is proved zero by the dense row itself. A concrete row
cache is admitted only through equality with this exhaustive finite traversal;
neither the dense matrix nor the genuine Nat raising operator is redefined. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
namespace TorusLean.BosonFiniteCertificate
open Matrix
open scoped BigOperators

def natFourDenseSparseRow {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℚ)
    (i : Fin m) : List (Fin n × ℚ) :=
  ((List.finRange n).filter fun k => decide (A i k ≠ 0)).map fun k => (k,A i k)

def natFourSparseRowProduct {n r : ℕ} (row : List (Fin n × ℚ))
    (B : Matrix (Fin n) (Fin r) ℚ) (j : Fin r) : ℚ :=
  (row.map fun kv => kv.2 * B kv.1 j).sum

private theorem natFourDenseSparseRow_sum {n : ℕ}
    (a b : Fin n → ℚ) (l : List (Fin n)) :
    ((l.filter fun k => decide (a k ≠ 0)).map fun k => a k*b k).sum=
      (l.map fun k => a k*b k).sum := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    by_cases h : a k=0
    · simpa [h] using ih
    · simpa [h] using ih

theorem natFourSparseRowProduct_dense {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) (B : Matrix (Fin n) (Fin r) ℚ)
    (i : Fin m) (j : Fin r) :
    natFourSparseRowProduct (natFourDenseSparseRow A i) B j=(A*B) i j := by
  unfold natFourSparseRowProduct natFourDenseSparseRow
  simp only [List.map_map,Function.comp_def]
  rw [natFourDenseSparseRow_sum,← List.ofFn_eq_map,List.sum_ofFn]
  rfl

theorem natFourSparseRowProduct_matrix_check {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) ℚ) (B : Matrix (Fin n) (Fin r) ℚ)
    (D : Matrix (Fin m) (Fin r) ℚ) (rows : Fin m → List (Fin n × ℚ))
    (hrows : ∀ i, natFourDenseSparseRow A i=rows i)
    (hcheck : ∀ i j, natFourSparseRowProduct (rows i) B j=D i j) :
    A*B=D := by
  ext i j
  rw [← natFourSparseRowProduct_dense,hrows i]
  exact hcheck i j

#print axioms natFourSparseRowProduct_dense
#print axioms natFourSparseRowProduct_matrix_check
end TorusLean.BosonFiniteCertificate
