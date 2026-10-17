import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD13R5S13Row0 :
    OAI.Laughlin.Certificate.yRow 13 5 13
      (OAI.Laughlin.Certificate.rows[0]!) = (-603630375449497270875 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S13Row1 :
    OAI.Laughlin.Certificate.yRow 13 5 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((-3646125058788337843575 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S13Row2 :
    OAI.Laughlin.Certificate.yRow 13 5 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((-882417252664771824718575 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S13Row3 :
    OAI.Laughlin.Certificate.yRow 13 5 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((781331979965183524352475 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S13Row4 :
    OAI.Laughlin.Certificate.yRow 13 5 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((-3260988910047384083128275 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S13Row5 :
    OAI.Laughlin.Certificate.yRow 13 5 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-1064549773360076970841875 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD13R5S13Row6 :
    OAI.Laughlin.Certificate.yRow 13 5 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-209323066691221002394875 / 32768) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD13R5S13 :
    OAI.Laughlin.Certificate.errorRational 13 (2 : Fin 7) (6 : Fin 7) =
      TorusLean.FermionM3.errorTable13 (2 : Fin 7) (6 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 13 5 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD13R5S13Row0,
    originalYRowSplitD13R5S13Row1,
    originalYRowSplitD13R5S13Row2,
    originalYRowSplitD13R5S13Row3,
    originalYRowSplitD13R5S13Row4,
    originalYRowSplitD13R5S13Row5,
    originalYRowSplitD13R5S13Row6]
  norm_num [TorusLean.FermionM3.errorTable13]

#print axioms originalYEntrySplitD13R5S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
