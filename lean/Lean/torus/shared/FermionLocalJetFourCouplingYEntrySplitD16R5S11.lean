import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R5S11Row0 :
    OAI.Laughlin.Certificate.yRow 16 5 11
      (OAI.Laughlin.Certificate.rows[0]!) = (945859550564142348750 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S11Row1 :
    OAI.Laughlin.Certificate.yRow 16 5 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((485009113024241623125 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S11Row2 :
    OAI.Laughlin.Certificate.yRow 16 5 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((-42954662490889664851875 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S11Row3 :
    OAI.Laughlin.Certificate.yRow 16 5 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((2370732675008967614874375 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S11Row4 :
    OAI.Laughlin.Certificate.yRow 16 5 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-3508464885121408222085625 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S11Row5 :
    OAI.Laughlin.Certificate.yRow 16 5 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((10664808266810635660490625 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R5S11Row6 :
    OAI.Laughlin.Certificate.yRow 16 5 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((40190447557905290848125 / 512) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R5S11 :
    OAI.Laughlin.Certificate.errorRational 16 (2 : Fin 8) (5 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (2 : Fin 8) (5 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 5 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R5S11Row0,
    originalYRowSplitD16R5S11Row1,
    originalYRowSplitD16R5S11Row2,
    originalYRowSplitD16R5S11Row3,
    originalYRowSplitD16R5S11Row4,
    originalYRowSplitD16R5S11Row5,
    originalYRowSplitD16R5S11Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R5S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
