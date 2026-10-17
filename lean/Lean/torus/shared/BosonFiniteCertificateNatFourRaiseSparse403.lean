import torus.shared.BosonFiniteCertificateNatFourSparseRaiseProductCore
import torus.shared.BosonFiniteCertificateNatFourRaise403

/-! Checked exhaustive row cache of the original dense raising matrix.
Every omitted column is proved zero by the full finite traversal. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
namespace TorusLean.BosonFiniteCertificate
open Matrix

def f403raiseSparseRows : Fin 5 → List (Fin 3 × ℚ) :=
  ![[(0, 1)],
    [(0, 3), (1, 1)],
    [(1, 1)],
    [(1, 2), (2, 3)],
    [(2, 1)]]

theorem f403_raise_sparse_rows_check : ∀ i : Fin 5,
    natFourDenseSparseRow f403raise i=f403raiseSparseRows i := by
  intro i
  fin_cases i <;> decide +kernel

#print axioms f403_raise_sparse_rows_check
end TorusLean.BosonFiniteCertificate
