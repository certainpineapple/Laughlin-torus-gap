import torus.shared.BosonFiniteCertificateNatFourSparseRaiseProductCore
import torus.shared.BosonFiniteCertificateNatFourRaise414

/-! A checked row cache of the original dense degree14-to15 raising matrix.
The exhaustive dense-row equality is the proof obligation; no zero entry is
assumed and no coordinate or Nat operator is changed. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
namespace TorusLean.BosonFiniteCertificate
open Matrix

def f414raiseSparseRows : Fin 54 → List (Fin 47 × ℚ) :=
  ![[(0, 1)],
    [(0, 3), (1, 1)],
    [(1, 1), (2, 1)],
    [(2, 1), (3, 1)],
    [(3, 1), (4, 1)],
    [(4, 1), (5, 1)],
    [(5, 1), (6, 1)],
    [(6, 1), (7, 2)],
    [(1, 2), (8, 1)],
    [(2, 2), (8, 2), (9, 1)],
    [(3, 2), (9, 1), (10, 1)],
    [(4, 2), (10, 1), (11, 1)],
    [(5, 2), (11, 1), (12, 1)],
    [(6, 2), (12, 1), (13, 1)],
    [(7, 2), (13, 1)],
    [(9, 1), (14, 1)],
    [(10, 1), (14, 2), (15, 1)],
    [(11, 1), (15, 1), (16, 1)],
    [(12, 1), (16, 1), (17, 1)],
    [(13, 1), (17, 1), (18, 2)],
    [(15, 1), (19, 1)],
    [(16, 1), (19, 2), (20, 1)],
    [(17, 1), (20, 1), (21, 1)],
    [(18, 1), (21, 1)],
    [(20, 1), (22, 1)],
    [(21, 1), (22, 2), (23, 2)],
    [(23, 1)],
    [(8, 1), (24, 1)],
    [(9, 1), (24, 3), (25, 1)],
    [(10, 1), (25, 1), (26, 1)],
    [(11, 1), (26, 1), (27, 1)],
    [(12, 1), (27, 1), (28, 1)],
    [(13, 1), (28, 1), (29, 2)],
    [(14, 1), (25, 2), (30, 1)],
    [(15, 1), (26, 2), (30, 2), (31, 1)],
    [(16, 1), (27, 2), (31, 1), (32, 1)],
    [(17, 1), (28, 2), (32, 1), (33, 1)],
    [(18, 1), (29, 2), (33, 1)],
    [(19, 1), (31, 1), (34, 1)],
    [(20, 1), (32, 1), (34, 2), (35, 1)],
    [(21, 1), (33, 1), (35, 1), (36, 2)],
    [(22, 1), (35, 1), (37, 1)],
    [(23, 1), (36, 1), (37, 2)],
    [(30, 1), (38, 1)],
    [(31, 1), (38, 3), (39, 1)],
    [(32, 1), (39, 1), (40, 1)],
    [(33, 1), (40, 1), (41, 2)],
    [(34, 1), (39, 2), (42, 1)],
    [(35, 1), (40, 2), (42, 2), (43, 1)],
    [(36, 1), (41, 2), (43, 1)],
    [(37, 1), (43, 1), (44, 3)],
    [(42, 1), (45, 1)],
    [(43, 1), (45, 3), (46, 2)],
    [(44, 1), (46, 2)]]

theorem f414_raise_sparse_rows_check : ∀ i : Fin 54,
    natFourDenseSparseRow f414raise i=f414raiseSparseRows i := by
  intro i
  fin_cases i <;> decide +kernel

#print axioms f414_raise_sparse_rows_check
end TorusLean.BosonFiniteCertificate
