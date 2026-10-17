import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD17R5S13Row0 :
    OAI.Laughlin.Certificate.yRow 17 5 13
      (OAI.Laughlin.Certificate.rows[0]!) = (0 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S13Row1 :
    OAI.Laughlin.Certificate.yRow 17 5 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((2734188618785150401875 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S13Row2 :
    OAI.Laughlin.Certificate.yRow 17 5 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((-1565127513489989661337125 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S13Row3 :
    OAI.Laughlin.Certificate.yRow 17 5 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((-173284637209936859982375 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S13Row4 :
    OAI.Laughlin.Certificate.yRow 17 5 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((73532122268250731727695625 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S13Row5 :
    OAI.Laughlin.Certificate.yRow 17 5 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-94633315840407519490404375 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD17R5S13Row6 :
    OAI.Laughlin.Certificate.yRow 17 5 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((225978040949595771461625 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD17R5S13 :
    OAI.Laughlin.Certificate.errorRational 17 (2 : Fin 9) (6 : Fin 9) =
      TorusLean.FermionM3.errorTable17 (2 : Fin 9) (6 : Fin 9) := by
  change OAI.Laughlin.Certificate.Y 17 5 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD17R5S13Row0,
    originalYRowSplitD17R5S13Row1,
    originalYRowSplitD17R5S13Row2,
    originalYRowSplitD17R5S13Row3,
    originalYRowSplitD17R5S13Row4,
    originalYRowSplitD17R5S13Row5,
    originalYRowSplitD17R5S13Row6]
  norm_num [TorusLean.FermionM3.errorTable17]

#print axioms originalYEntrySplitD17R5S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
