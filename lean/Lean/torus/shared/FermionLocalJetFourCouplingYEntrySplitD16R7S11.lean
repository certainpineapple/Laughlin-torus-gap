import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R7S11Row0 :
    OAI.Laughlin.Certificate.yRow 16 7 11
      (OAI.Laughlin.Certificate.rows[0]!) = (-2831230471213423125 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S11Row1 :
    OAI.Laughlin.Certificate.yRow 16 7 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((-21621073836086195625 / 64) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S11Row2 :
    OAI.Laughlin.Certificate.yRow 16 7 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((-59812182073757643886125 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S11Row3 :
    OAI.Laughlin.Certificate.yRow 16 7 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((-1812535096685066227348875 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S11Row4 :
    OAI.Laughlin.Certificate.yRow 16 7 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-247880510421291312555375 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S11Row5 :
    OAI.Laughlin.Certificate.yRow 16 7 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((-2892479465115820107383625 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R7S11Row6 :
    OAI.Laughlin.Certificate.yRow 16 7 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-49560691549909415077125 / 2048) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R7S11 :
    OAI.Laughlin.Certificate.errorRational 16 (3 : Fin 8) (5 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (3 : Fin 8) (5 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 7 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R7S11Row0,
    originalYRowSplitD16R7S11Row1,
    originalYRowSplitD16R7S11Row2,
    originalYRowSplitD16R7S11Row3,
    originalYRowSplitD16R7S11Row4,
    originalYRowSplitD16R7S11Row5,
    originalYRowSplitD16R7S11Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R7S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
