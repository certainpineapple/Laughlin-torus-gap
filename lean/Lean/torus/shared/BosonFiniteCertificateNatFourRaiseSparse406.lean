import torus.shared.BosonFiniteCertificateNatFourSparseRaiseProductCore
import torus.shared.BosonFiniteCertificateNatFourRaise406

/-! Checked exhaustive row cache of the original dense raising matrix.
Every omitted column is proved zero by the full finite traversal. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
namespace TorusLean.BosonFiniteCertificate
open Matrix

def f406raiseSparseRows : Fin 11 → List (Fin 9 × ℚ) :=
  ![[(0, 1)],
    [(0, 3), (1, 1)],
    [(1, 1), (2, 1)],
    [(2, 1), (3, 2)],
    [(1, 2), (4, 1)],
    [(2, 2), (4, 2), (5, 1)],
    [(3, 2), (5, 1)],
    [(5, 1), (6, 3)],
    [(4, 1), (7, 1)],
    [(5, 1), (7, 3), (8, 2)],
    [(6, 1), (8, 2)]]

theorem f406_raise_sparse_rows_check : ∀ i : Fin 11,
    natFourDenseSparseRow f406raise i=f406raiseSparseRows i := by
  intro i
  fin_cases i <;> decide +kernel

#print axioms f406_raise_sparse_rows_check
end TorusLean.BosonFiniteCertificate
