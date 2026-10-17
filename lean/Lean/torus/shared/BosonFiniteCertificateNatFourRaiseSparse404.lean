import torus.shared.BosonFiniteCertificateNatFourSparseRaiseProductCore
import torus.shared.BosonFiniteCertificateNatFourRaise404

/-! Checked exhaustive row cache of the original dense raising matrix.
Every omitted column is proved zero by the full finite traversal. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
namespace TorusLean.BosonFiniteCertificate
open Matrix

def f404raiseSparseRows : Fin 6 → List (Fin 5 × ℚ) :=
  ![[(0, 1)],
    [(0, 3), (1, 1)],
    [(1, 1), (2, 2)],
    [(1, 2), (3, 1)],
    [(2, 2), (3, 2)],
    [(3, 1), (4, 4)]]

theorem f404_raise_sparse_rows_check : ∀ i : Fin 6,
    natFourDenseSparseRow f404raise i=f404raiseSparseRows i := by
  intro i
  fin_cases i <;> decide +kernel

#print axioms f404_raise_sparse_rows_check
end TorusLean.BosonFiniteCertificate
