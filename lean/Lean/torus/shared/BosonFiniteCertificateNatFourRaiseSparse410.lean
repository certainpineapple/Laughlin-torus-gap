import torus.shared.BosonFiniteCertificateNatFourSparseRaiseProductCore
import torus.shared.BosonFiniteCertificateNatFourRaise410

/-! Checked exhaustive row cache of the original dense raising matrix.
Every omitted column is proved zero by the full finite traversal. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
namespace TorusLean.BosonFiniteCertificate
open Matrix

def f410raiseSparseRows : Fin 27 → List (Fin 23 × ℚ) :=
  ![[(0, 1)],
    [(0, 3), (1, 1)],
    [(1, 1), (2, 1)],
    [(2, 1), (3, 1)],
    [(3, 1), (4, 1)],
    [(4, 1), (5, 2)],
    [(1, 2), (6, 1)],
    [(2, 2), (6, 2), (7, 1)],
    [(3, 2), (7, 1), (8, 1)],
    [(4, 2), (8, 1), (9, 1)],
    [(5, 2), (9, 1)],
    [(7, 1), (10, 1)],
    [(8, 1), (10, 2), (11, 1)],
    [(9, 1), (11, 1), (12, 2)],
    [(11, 1), (13, 1)],
    [(12, 1), (13, 2)],
    [(6, 1), (14, 1)],
    [(7, 1), (14, 3), (15, 1)],
    [(8, 1), (15, 1), (16, 1)],
    [(9, 1), (16, 1), (17, 2)],
    [(10, 1), (15, 2), (18, 1)],
    [(11, 1), (16, 2), (18, 2), (19, 1)],
    [(12, 1), (17, 2), (19, 1)],
    [(13, 1), (19, 1), (20, 3)],
    [(18, 1), (21, 1)],
    [(19, 1), (21, 3), (22, 2)],
    [(20, 1), (22, 2)]]

theorem f410_raise_sparse_rows_check : ∀ i : Fin 27,
    natFourDenseSparseRow f410raise i=f410raiseSparseRows i := by
  intro i
  fin_cases i <;> decide +kernel

#print axioms f410_raise_sparse_rows_check
end TorusLean.BosonFiniteCertificate
