import torus.shared.BosonFiniteCertificateNatFourSparseRaiseProductCore
import torus.shared.BosonFiniteCertificateNatFourRaise409

/-! Checked exhaustive row cache of the original dense raising matrix.
Every omitted column is proved zero by the full finite traversal. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
namespace TorusLean.BosonFiniteCertificate
open Matrix

def f409raiseSparseRows : Fin 23 → List (Fin 18 × ℚ) :=
  ![[(0, 1)],
    [(0, 3), (1, 1)],
    [(1, 1), (2, 1)],
    [(2, 1), (3, 1)],
    [(3, 1), (4, 1)],
    [(4, 1)],
    [(1, 2), (5, 1)],
    [(2, 2), (5, 2), (6, 1)],
    [(3, 2), (6, 1), (7, 1)],
    [(4, 2), (7, 1), (8, 2)],
    [(6, 1), (9, 1)],
    [(7, 1), (9, 2), (10, 1)],
    [(8, 1), (10, 1)],
    [(10, 1), (11, 3)],
    [(5, 1), (12, 1)],
    [(6, 1), (12, 3), (13, 1)],
    [(7, 1), (13, 1), (14, 1)],
    [(8, 1), (14, 1)],
    [(9, 1), (13, 2), (15, 1)],
    [(10, 1), (14, 2), (15, 2), (16, 2)],
    [(11, 1), (16, 1)],
    [(15, 1), (17, 1)],
    [(16, 1), (17, 3)]]

theorem f409_raise_sparse_rows_check : ∀ i : Fin 23,
    natFourDenseSparseRow f409raise i=f409raiseSparseRows i := by
  intro i
  fin_cases i <;> decide +kernel

#print axioms f409_raise_sparse_rows_check
end TorusLean.BosonFiniteCertificate
