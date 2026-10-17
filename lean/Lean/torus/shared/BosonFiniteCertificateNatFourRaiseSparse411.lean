import torus.shared.BosonFiniteCertificateNatFourSparseRaiseProductCore
import torus.shared.BosonFiniteCertificateNatFourRaise411

/-! Checked exhaustive row cache of the original dense raising matrix.
Every omitted column is proved zero by the full finite traversal. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
namespace TorusLean.BosonFiniteCertificate
open Matrix

def f411raiseSparseRows : Fin 34 → List (Fin 27 × ℚ) :=
  ![[(0, 1)],
    [(0, 3), (1, 1)],
    [(1, 1), (2, 1)],
    [(2, 1), (3, 1)],
    [(3, 1), (4, 1)],
    [(4, 1), (5, 1)],
    [(5, 1)],
    [(1, 2), (6, 1)],
    [(2, 2), (6, 2), (7, 1)],
    [(3, 2), (7, 1), (8, 1)],
    [(4, 2), (8, 1), (9, 1)],
    [(5, 2), (9, 1), (10, 2)],
    [(7, 1), (11, 1)],
    [(8, 1), (11, 2), (12, 1)],
    [(9, 1), (12, 1), (13, 1)],
    [(10, 1), (13, 1)],
    [(12, 1), (14, 1)],
    [(13, 1), (14, 2), (15, 2)],
    [(15, 1)],
    [(6, 1), (16, 1)],
    [(7, 1), (16, 3), (17, 1)],
    [(8, 1), (17, 1), (18, 1)],
    [(9, 1), (18, 1), (19, 1)],
    [(10, 1), (19, 1)],
    [(11, 1), (17, 2), (20, 1)],
    [(12, 1), (18, 2), (20, 2), (21, 1)],
    [(13, 1), (19, 2), (21, 1), (22, 2)],
    [(14, 1), (21, 1), (23, 1)],
    [(15, 1), (22, 1), (23, 2)],
    [(20, 1), (24, 1)],
    [(21, 1), (24, 3), (25, 1)],
    [(22, 1), (25, 1)],
    [(23, 1), (25, 2), (26, 3)],
    [(26, 1)]]

theorem f411_raise_sparse_rows_check : ∀ i : Fin 34,
    natFourDenseSparseRow f411raise i=f411raiseSparseRows i := by
  intro i
  fin_cases i <;> decide +kernel

#print axioms f411_raise_sparse_rows_check
end TorusLean.BosonFiniteCertificate
