import torus.shared.BosonFiniteCertificateNatFourSparseRaiseProductCore
import torus.shared.BosonFiniteCertificateNatFourRaise412

/-! Checked exhaustive row cache of the original dense raising matrix.
Every omitted column is proved zero by the full finite traversal. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
namespace TorusLean.BosonFiniteCertificate
open Matrix

def f412raiseSparseRows : Fin 39 → List (Fin 34 × ℚ) :=
  ![[(0, 1)],
    [(0, 3), (1, 1)],
    [(1, 1), (2, 1)],
    [(2, 1), (3, 1)],
    [(3, 1), (4, 1)],
    [(4, 1), (5, 1)],
    [(5, 1), (6, 2)],
    [(1, 2), (7, 1)],
    [(2, 2), (7, 2), (8, 1)],
    [(3, 2), (8, 1), (9, 1)],
    [(4, 2), (9, 1), (10, 1)],
    [(5, 2), (10, 1), (11, 1)],
    [(6, 2), (11, 1)],
    [(8, 1), (12, 1)],
    [(9, 1), (12, 2), (13, 1)],
    [(10, 1), (13, 1), (14, 1)],
    [(11, 1), (14, 1), (15, 2)],
    [(13, 1), (16, 1)],
    [(14, 1), (16, 2), (17, 1)],
    [(15, 1), (17, 1)],
    [(17, 1), (18, 3)],
    [(7, 1), (19, 1)],
    [(8, 1), (19, 3), (20, 1)],
    [(9, 1), (20, 1), (21, 1)],
    [(10, 1), (21, 1), (22, 1)],
    [(11, 1), (22, 1), (23, 2)],
    [(12, 1), (20, 2), (24, 1)],
    [(13, 1), (21, 2), (24, 2), (25, 1)],
    [(14, 1), (22, 2), (25, 1), (26, 1)],
    [(15, 1), (23, 2), (26, 1)],
    [(16, 1), (25, 1), (27, 1)],
    [(17, 1), (26, 1), (27, 2), (28, 2)],
    [(18, 1), (28, 1)],
    [(24, 1), (29, 1)],
    [(25, 1), (29, 3), (30, 1)],
    [(26, 1), (30, 1), (31, 2)],
    [(27, 1), (30, 2), (32, 1)],
    [(28, 1), (31, 2), (32, 2)],
    [(32, 1), (33, 4)]]

theorem f412_raise_sparse_rows_check : ∀ i : Fin 39,
    natFourDenseSparseRow f412raise i=f412raiseSparseRows i := by
  intro i
  fin_cases i <;> decide +kernel

#print axioms f412_raise_sparse_rows_check
end TorusLean.BosonFiniteCertificate
