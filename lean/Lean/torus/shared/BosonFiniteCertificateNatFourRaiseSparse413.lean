import torus.shared.BosonFiniteCertificateNatFourSparseRaiseProductCore
import torus.shared.BosonFiniteCertificateNatFourRaise413

/-! Checked exhaustive row cache of the original dense raising matrix.
Every omitted column is proved zero by the full finite traversal. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
namespace TorusLean.BosonFiniteCertificate
open Matrix

def f413raiseSparseRows : Fin 47 → List (Fin 39 × ℚ) :=
  ![[(0, 1)],
    [(0, 3), (1, 1)],
    [(1, 1), (2, 1)],
    [(2, 1), (3, 1)],
    [(3, 1), (4, 1)],
    [(4, 1), (5, 1)],
    [(5, 1), (6, 1)],
    [(6, 1)],
    [(1, 2), (7, 1)],
    [(2, 2), (7, 2), (8, 1)],
    [(3, 2), (8, 1), (9, 1)],
    [(4, 2), (9, 1), (10, 1)],
    [(5, 2), (10, 1), (11, 1)],
    [(6, 2), (11, 1), (12, 2)],
    [(8, 1), (13, 1)],
    [(9, 1), (13, 2), (14, 1)],
    [(10, 1), (14, 1), (15, 1)],
    [(11, 1), (15, 1), (16, 1)],
    [(12, 1), (16, 1)],
    [(14, 1), (17, 1)],
    [(15, 1), (17, 2), (18, 1)],
    [(16, 1), (18, 1), (19, 2)],
    [(18, 1), (20, 1)],
    [(19, 1), (20, 2)],
    [(7, 1), (21, 1)],
    [(8, 1), (21, 3), (22, 1)],
    [(9, 1), (22, 1), (23, 1)],
    [(10, 1), (23, 1), (24, 1)],
    [(11, 1), (24, 1), (25, 1)],
    [(12, 1), (25, 1)],
    [(13, 1), (22, 2), (26, 1)],
    [(14, 1), (23, 2), (26, 2), (27, 1)],
    [(15, 1), (24, 2), (27, 1), (28, 1)],
    [(16, 1), (25, 2), (28, 1), (29, 2)],
    [(17, 1), (27, 1), (30, 1)],
    [(18, 1), (28, 1), (30, 2), (31, 1)],
    [(19, 1), (29, 1), (31, 1)],
    [(20, 1), (31, 1), (32, 3)],
    [(26, 1), (33, 1)],
    [(27, 1), (33, 3), (34, 1)],
    [(28, 1), (34, 1), (35, 1)],
    [(29, 1), (35, 1)],
    [(30, 1), (34, 2), (36, 1)],
    [(31, 1), (35, 2), (36, 2), (37, 2)],
    [(32, 1), (37, 1)],
    [(36, 1), (38, 1)],
    [(37, 1), (38, 3)]]

theorem f413_raise_sparse_rows_check : ∀ i : Fin 47,
    natFourDenseSparseRow f413raise i=f413raiseSparseRows i := by
  intro i
  fin_cases i <;> decide +kernel

#print axioms f413_raise_sparse_rows_check
end TorusLean.BosonFiniteCertificate
