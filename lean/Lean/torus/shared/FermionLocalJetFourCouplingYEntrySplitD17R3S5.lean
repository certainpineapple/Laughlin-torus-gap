import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R3S5Row0 :
    OAI.Laughlin.Certificate.yRow 17 3 5
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S5Row1 :
    OAI.Laughlin.Certificate.yRow 17 3 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((-433693333594254857248125 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S5Row2 :
    OAI.Laughlin.Certificate.yRow 17 3 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((-29192573615782222962941625 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S5Row3 :
    OAI.Laughlin.Certificate.yRow 17 3 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((4090052219459968156019625 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S5Row4 :
    OAI.Laughlin.Certificate.yRow 17 3 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((-2587659083852723523351583875 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S5Row5 :
    OAI.Laughlin.Certificate.yRow 17 3 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((1290400504592958796796884125 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R3S5Row6 :
    OAI.Laughlin.Certificate.yRow 17 3 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((3907130776130467130119875 / 65536) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R3S5 :
    OAI.Laughlin.Certificate.errorRational 17 (1 : Fin 9) (2 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (1 : Fin 9) (2 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 3 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R3S5Row0,
    originalYRowSplitD17R3S5Row1,
    originalYRowSplitD17R3S5Row2,
    originalYRowSplitD17R3S5Row3,
    originalYRowSplitD17R3S5Row4,
    originalYRowSplitD17R3S5Row5,
    originalYRowSplitD17R3S5Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R3S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
