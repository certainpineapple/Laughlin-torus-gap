import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R11S13Row0 :
    OAI.Laughlin.Certificate.yRow 15 11 13
      (OAI.Laughlin.Certificate.rows[0]!) = (3082255122124325347200 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R11S13Row1 :
    OAI.Laughlin.Certificate.yRow 15 11 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((655793678494678548825 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R11S13Row2 :
    OAI.Laughlin.Certificate.yRow 15 11 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((-291969917547977496002175 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R11S13Row3 :
    OAI.Laughlin.Certificate.yRow 15 11 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((74209335219286923330675 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R11S13Row4 :
    OAI.Laughlin.Certificate.yRow 15 11 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((1204247803314177716254875 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R11S13Row5 :
    OAI.Laughlin.Certificate.yRow 15 11 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-92283903979719631940475 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R11S13Row6 :
    OAI.Laughlin.Certificate.yRow 15 11 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((-5062199411164820549625 / 128) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R11S13 :
    OAI.Laughlin.Certificate.errorRational 15 (5 : Fin 8) (6 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (5 : Fin 8) (6 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 11 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R11S13Row0,
    originalYRowSplitD15R11S13Row1,
    originalYRowSplitD15R11S13Row2,
    originalYRowSplitD15R11S13Row3,
    originalYRowSplitD15R11S13Row4,
    originalYRowSplitD15R11S13Row5,
    originalYRowSplitD15R11S13Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R11S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
