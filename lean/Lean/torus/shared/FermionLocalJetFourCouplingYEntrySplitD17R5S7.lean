import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R5S7Row0 :
    OAI.Laughlin.Certificate.yRow 17 5 7
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S7Row1 :
    OAI.Laughlin.Certificate.yRow 17 5 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((-3793315298634760696875 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S7Row2 :
    OAI.Laughlin.Certificate.yRow 17 5 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((-4925010546592473746784375 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S7Row3 :
    OAI.Laughlin.Certificate.yRow 17 5 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((-801008999430609976689375 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S7Row4 :
    OAI.Laughlin.Certificate.yRow 17 5 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-28886038407210915847310625 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S7Row5 :
    OAI.Laughlin.Certificate.yRow 17 5 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((561452861488806281090683125 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S7Row6 :
    OAI.Laughlin.Certificate.yRow 17 5 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((2782285192286862263780625 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R5S7 :
    OAI.Laughlin.Certificate.errorRational 17 (2 : Fin 9) (3 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (2 : Fin 9) (3 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 5 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R5S7Row0,
    originalYRowSplitD17R5S7Row1,
    originalYRowSplitD17R5S7Row2,
    originalYRowSplitD17R5S7Row3,
    originalYRowSplitD17R5S7Row4,
    originalYRowSplitD17R5S7Row5,
    originalYRowSplitD17R5S7Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R5S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
