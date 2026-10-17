import torus.shared.BosonFiniteCertificateNatFourSparseRaiseProductCore
import torus.shared.BosonFiniteCertificateNatFourRaise407

/-! Checked exhaustive row cache of the original dense raising matrix.
Every omitted column is proved zero by the full finite traversal. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
namespace TorusLean.BosonFiniteCertificate
open Matrix

def f407raiseSparseRows : Fin 15 → List (Fin 11 × ℚ) :=
  ![[(0, 1)],
    [(0, 3), (1, 1)],
    [(1, 1), (2, 1)],
    [(2, 1), (3, 1)],
    [(3, 1)],
    [(1, 2), (4, 1)],
    [(2, 2), (4, 2), (5, 1)],
    [(3, 2), (5, 1), (6, 2)],
    [(5, 1), (7, 1)],
    [(6, 1), (7, 2)],
    [(4, 1), (8, 1)],
    [(5, 1), (8, 3), (9, 1)],
    [(6, 1), (9, 1)],
    [(7, 1), (9, 2), (10, 3)],
    [(10, 1)]]

theorem f407_raise_sparse_rows_check : ∀ i : Fin 15,
    natFourDenseSparseRow f407raise i=f407raiseSparseRows i := by
  intro i
  fin_cases i <;> decide +kernel

#print axioms f407_raise_sparse_rows_check
end TorusLean.BosonFiniteCertificate
