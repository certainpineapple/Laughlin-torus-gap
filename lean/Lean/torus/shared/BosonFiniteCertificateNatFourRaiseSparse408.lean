import torus.shared.BosonFiniteCertificateNatFourSparseRaiseProductCore
import torus.shared.BosonFiniteCertificateNatFourRaise408

/-! Checked exhaustive row cache of the original dense raising matrix.
Every omitted column is proved zero by the full finite traversal. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
namespace TorusLean.BosonFiniteCertificate
open Matrix

def f408raiseSparseRows : Fin 18 → List (Fin 15 × ℚ) :=
  ![[(0, 1)],
    [(0, 3), (1, 1)],
    [(1, 1), (2, 1)],
    [(2, 1), (3, 1)],
    [(3, 1), (4, 2)],
    [(1, 2), (5, 1)],
    [(2, 2), (5, 2), (6, 1)],
    [(3, 2), (6, 1), (7, 1)],
    [(4, 2), (7, 1)],
    [(6, 1), (8, 1)],
    [(7, 1), (8, 2), (9, 2)],
    [(9, 1)],
    [(5, 1), (10, 1)],
    [(6, 1), (10, 3), (11, 1)],
    [(7, 1), (11, 1), (12, 2)],
    [(8, 1), (11, 2), (13, 1)],
    [(9, 1), (12, 2), (13, 2)],
    [(13, 1), (14, 4)]]

theorem f408_raise_sparse_rows_check : ∀ i : Fin 18,
    natFourDenseSparseRow f408raise i=f408raiseSparseRows i := by
  intro i
  fin_cases i <;> decide +kernel

#print axioms f408_raise_sparse_rows_check
end TorusLean.BosonFiniteCertificate
