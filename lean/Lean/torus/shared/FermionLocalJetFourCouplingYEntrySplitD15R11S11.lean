import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R11S11Row0 :
    OAI.Laughlin.Certificate.yRow 15 11 11
      (OAI.Laughlin.Certificate.rows[0]!) = (-457000454328164970300 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R11S11Row1 :
    OAI.Laughlin.Certificate.yRow 15 11 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((-252590682882555222975 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R11S11Row2 :
    OAI.Laughlin.Certificate.yRow 15 11 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((671733217649871313484625 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R11S11Row3 :
    OAI.Laughlin.Certificate.yRow 15 11 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((126666791128586112552225 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R11S11Row4 :
    OAI.Laughlin.Certificate.yRow 15 11 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((28378887720484087821375 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R11S11Row5 :
    OAI.Laughlin.Certificate.yRow 15 11 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((-2943655066208409231642975 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R11S11Row6 :
    OAI.Laughlin.Certificate.yRow 15 11 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-11198842347138803228025 / 128) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R11S11 :
    OAI.Laughlin.Certificate.errorRational 15 (5 : Fin 8) (5 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (5 : Fin 8) (5 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 11 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R11S11Row0,
    originalYRowSplitD15R11S11Row1,
    originalYRowSplitD15R11S11Row2,
    originalYRowSplitD15R11S11Row3,
    originalYRowSplitD15R11S11Row4,
    originalYRowSplitD15R11S11Row5,
    originalYRowSplitD15R11S11Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R11S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
