import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R7S9Row0 :
    OAI.Laughlin.Certificate.yRow 13 7 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((3319423074039600675 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R7S9Row1 :
    OAI.Laughlin.Certificate.yRow 13 7 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((7368046369575273225 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R7S9Row2 :
    OAI.Laughlin.Certificate.yRow 13 7 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((261414703468706471705025 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R7S9Row3 :
    OAI.Laughlin.Certificate.yRow 13 7 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((47581041000644769603825 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R7S9Row4 :
    OAI.Laughlin.Certificate.yRow 13 7 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((2693313159634085385375 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R7S9Row5 :
    OAI.Laughlin.Certificate.yRow 13 7 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((559584127039604591387025 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R7S9Row6 :
    OAI.Laughlin.Certificate.yRow 13 7 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-162774217526874154425 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD13R7S9 :
    OAI.Laughlin.Certificate.errorRational 13 (3 : Fin 7) (4 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (3 : Fin 7) (4 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 7 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R7S9Row0,
    originalYRowSplitD13R7S9Row1,
    originalYRowSplitD13R7S9Row2,
    originalYRowSplitD13R7S9Row3,
    originalYRowSplitD13R7S9Row4,
    originalYRowSplitD13R7S9Row5,
    originalYRowSplitD13R7S9Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R7S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
