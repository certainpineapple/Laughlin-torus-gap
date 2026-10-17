import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R11S11Row0 :
    OAI.Laughlin.Certificate.yRow 16 11 11
      (OAI.Laughlin.Certificate.rows[0]!) = (286098014956953622500 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R11S11Row1 :
    OAI.Laughlin.Certificate.yRow 16 11 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((2104387615575196875 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R11S11Row2 :
    OAI.Laughlin.Certificate.yRow 16 11 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((3172175772420180920625 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R11S11Row3 :
    OAI.Laughlin.Certificate.yRow 16 11 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((650654873641515098750625 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R11S11Row4 :
    OAI.Laughlin.Certificate.yRow 16 11 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((592502440708317917881125 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R11S11Row5 :
    OAI.Laughlin.Certificate.yRow 16 11 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((1682922639384582743923875 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R11S11Row6 :
    OAI.Laughlin.Certificate.yRow 16 11 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-155663529154919650470375 / 1024) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R11S11 :
    OAI.Laughlin.Certificate.errorRational 16 (5 : Fin 8) (5 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (5 : Fin 8) (5 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 11 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R11S11Row0,
    originalYRowSplitD16R11S11Row1,
    originalYRowSplitD16R11S11Row2,
    originalYRowSplitD16R11S11Row3,
    originalYRowSplitD16R11S11Row4,
    originalYRowSplitD16R11S11Row5,
    originalYRowSplitD16R11S11Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R11S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
