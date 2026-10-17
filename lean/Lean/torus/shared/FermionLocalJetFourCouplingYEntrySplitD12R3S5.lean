import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD12R3S5Row0 :
    OAI.Laughlin.Certificate.yRow 12 3 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((18841371887024982225 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S5Row1 :
    OAI.Laughlin.Certificate.yRow 12 3 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((15466129820707500225 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S5Row2 :
    OAI.Laughlin.Certificate.yRow 12 3 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((-347563323949692939527925 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S5Row3 :
    OAI.Laughlin.Certificate.yRow 12 3 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((237721048274739508636725 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S5Row4 :
    OAI.Laughlin.Certificate.yRow 12 3 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((-459216252732509026460775 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S5Row5 :
    OAI.Laughlin.Certificate.yRow 12 3 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((-21619641918501973312875 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R3S5Row6 :
    OAI.Laughlin.Certificate.yRow 12 3 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((-119145161792813708475 / 262144) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD12R3S5 :
    OAI.Laughlin.Certificate.errorRational 12 (1 : Fin 6) (2 : Fin 6) =
      TorusLean.FermionM3.errorTable12 (1 : Fin 6) (2 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 12 3 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD12R3S5Row0,
    originalYRowSplitD12R3S5Row1,
    originalYRowSplitD12R3S5Row2,
    originalYRowSplitD12R3S5Row3,
    originalYRowSplitD12R3S5Row4,
    originalYRowSplitD12R3S5Row5,
    originalYRowSplitD12R3S5Row6]
  norm_num [TorusLean.FermionM3.errorTable12]

#print axioms originalYEntrySplitD12R3S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
