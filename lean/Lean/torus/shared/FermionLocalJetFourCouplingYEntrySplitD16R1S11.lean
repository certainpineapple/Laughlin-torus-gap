import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R1S11Row0 :
    OAI.Laughlin.Certificate.yRow 16 1 11
      (OAI.Laughlin.Certificate.rows[0]!) = ((-161957680182772910060625 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S11Row1 :
    OAI.Laughlin.Certificate.yRow 16 1 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((-48878893853046440308125 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S11Row2 :
    OAI.Laughlin.Certificate.yRow 16 1 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((4041152532549116142283125 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S11Row3 :
    OAI.Laughlin.Certificate.yRow 16 1 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((172361510244239825580946875 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S11Row4 :
    OAI.Laughlin.Certificate.yRow 16 1 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-85651401846008657851817625 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S11Row5 :
    OAI.Laughlin.Certificate.yRow 16 1 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((372923996238286043030605125 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S11Row6 :
    OAI.Laughlin.Certificate.yRow 16 1 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-6907061024056358338548375 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R1S11 :
    OAI.Laughlin.Certificate.errorRational 16 (0 : Fin 8) (5 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (0 : Fin 8) (5 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 1 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R1S11Row0,
    originalYRowSplitD16R1S11Row1,
    originalYRowSplitD16R1S11Row2,
    originalYRowSplitD16R1S11Row3,
    originalYRowSplitD16R1S11Row4,
    originalYRowSplitD16R1S11Row5,
    originalYRowSplitD16R1S11Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R1S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
