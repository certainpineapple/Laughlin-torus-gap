import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R5S13Row0 :
    OAI.Laughlin.Certificate.yRow 16 5 13
      (OAI.Laughlin.Certificate.rows[0]!) = (4124191085201006820000 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S13Row1 :
    OAI.Laughlin.Certificate.yRow 16 5 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((966820632511647288375 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S13Row2 :
    OAI.Laughlin.Certificate.yRow 16 5 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((91992721494481347164625 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S13Row3 :
    OAI.Laughlin.Certificate.yRow 16 5 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((1231238618333620017746625 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S13Row4 :
    OAI.Laughlin.Certificate.yRow 16 5 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((817252114523871091440375 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S13Row5 :
    OAI.Laughlin.Certificate.yRow 16 5 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-50438575660492454239072125 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S13Row6 :
    OAI.Laughlin.Certificate.yRow 16 5 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-16913474802374388863625 / 1024) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R5S13 :
    OAI.Laughlin.Certificate.errorRational 16 (2 : Fin 8) (6 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (2 : Fin 8) (6 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 5 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R5S13Row0,
    originalYRowSplitD16R5S13Row1,
    originalYRowSplitD16R5S13Row2,
    originalYRowSplitD16R5S13Row3,
    originalYRowSplitD16R5S13Row4,
    originalYRowSplitD16R5S13Row5,
    originalYRowSplitD16R5S13Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R5S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
