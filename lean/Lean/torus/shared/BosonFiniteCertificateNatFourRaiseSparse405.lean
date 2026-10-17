import torus.shared.BosonFiniteCertificateNatFourSparseRaiseProductCore
import torus.shared.BosonFiniteCertificateNatFourRaise405

/-! Checked exhaustive row cache of the original dense raising matrix.
Every omitted column is proved zero by the full finite traversal. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
namespace TorusLean.BosonFiniteCertificate
open Matrix

def f405raiseSparseRows : Fin 9 → List (Fin 6 × ℚ) :=
  ![[(0, 1)],
    [(0, 3), (1, 1)],
    [(1, 1), (2, 1)],
    [(2, 1)],
    [(1, 2), (3, 1)],
    [(2, 2), (3, 2), (4, 2)],
    [(4, 1)],
    [(3, 1), (5, 1)],
    [(4, 1), (5, 3)]]

theorem f405_raise_sparse_rows_check : ∀ i : Fin 9,
    natFourDenseSparseRow f405raise i=f405raiseSparseRows i := by
  intro i
  fin_cases i <;> decide +kernel

#print axioms f405_raise_sparse_rows_check
end TorusLean.BosonFiniteCertificate
