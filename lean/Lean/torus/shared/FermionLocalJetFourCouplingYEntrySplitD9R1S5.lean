import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD9R1S5Row0 :
    OAI.Laughlin.Certificate.yRow 9 1 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((661529479417998975 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S5Row1 :
    OAI.Laughlin.Certificate.yRow 9 1 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((61625069783226784989 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S5Row2 :
    OAI.Laughlin.Certificate.yRow 9 1 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((7133328454998280304565 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S5Row3 :
    OAI.Laughlin.Certificate.yRow 9 1 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((6209075185929566853735 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S5Row4 :
    OAI.Laughlin.Certificate.yRow 9 1 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((24808037692100797820985 / 16777216) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S5Row5 :
    OAI.Laughlin.Certificate.yRow 9 1 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((273097314790774595015685 / 67108864) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD9R1S5Row6 :
    OAI.Laughlin.Certificate.yRow 9 1 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-5721518735276892362325 / 8388608) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD9R1S5 :
    OAI.Laughlin.Certificate.errorRational 9 (0 : Fin 5) (2 : Fin 5) =
      TorusLean.FermionM3.errorTable09 (0 : Fin 5) (2 : Fin 5) := by
  change OAI.Laughlin.Certificate.Y 9 1 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD9R1S5Row0,
    originalYRowSplitD9R1S5Row1,
    originalYRowSplitD9R1S5Row2,
    originalYRowSplitD9R1S5Row3,
    originalYRowSplitD9R1S5Row4,
    originalYRowSplitD9R1S5Row5,
    originalYRowSplitD9R1S5Row6]
  norm_num [TorusLean.FermionM3.errorTable09]

#print axioms originalYEntrySplitD9R1S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
