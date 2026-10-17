import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R3S13Row0 :
    OAI.Laughlin.Certificate.yRow 16 3 13
      (OAI.Laughlin.Certificate.rows[0]!) = (-12055679493060653950500 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S13Row1 :
    OAI.Laughlin.Certificate.yRow 16 3 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((46123836112306277325 / 512) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S13Row2 :
    OAI.Laughlin.Certificate.yRow 16 3 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((-4352507077585661650881225 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S13Row3 :
    OAI.Laughlin.Certificate.yRow 16 3 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((-17412778027523291126538825 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S13Row4 :
    OAI.Laughlin.Certificate.yRow 16 3 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((44892430815532587498943875 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S13Row5 :
    OAI.Laughlin.Certificate.yRow 16 3 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((-5117985308534949557152875 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R3S13Row6 :
    OAI.Laughlin.Certificate.yRow 16 3 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((715156579460186058870675 / 2048) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R3S13 :
    OAI.Laughlin.Certificate.errorRational 16 (1 : Fin 8) (6 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (1 : Fin 8) (6 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 3 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R3S13Row0,
    originalYRowSplitD16R3S13Row1,
    originalYRowSplitD16R3S13Row2,
    originalYRowSplitD16R3S13Row3,
    originalYRowSplitD16R3S13Row4,
    originalYRowSplitD16R3S13Row5,
    originalYRowSplitD16R3S13Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R3S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
