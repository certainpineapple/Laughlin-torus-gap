import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R3S13Row0 :
    OAI.Laughlin.Certificate.yRow 14 3 13
      (OAI.Laughlin.Certificate.rows[0]!) = ((9357158908476376922925 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S13Row1 :
    OAI.Laughlin.Certificate.yRow 14 3 13
      (OAI.Laughlin.Certificate.rows[1]!) = ((15564485379750276694725 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S13Row2 :
    OAI.Laughlin.Certificate.yRow 14 3 13
      (OAI.Laughlin.Certificate.rows[2]!) = ((19086026582692763793324225 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S13Row3 :
    OAI.Laughlin.Certificate.yRow 14 3 13
      (OAI.Laughlin.Certificate.rows[3]!) = ((-1470463703567283845244825 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S13Row4 :
    OAI.Laughlin.Certificate.yRow 14 3 13
      (OAI.Laughlin.Certificate.rows[4]!) = ((-24266049589447094951925975 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S13Row5 :
    OAI.Laughlin.Certificate.yRow 14 3 13
      (OAI.Laughlin.Certificate.rows[5]!) = ((14471816835145237299614025 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S13Row6 :
    OAI.Laughlin.Certificate.yRow 14 3 13
      (OAI.Laughlin.Certificate.rows[6]!) = ((515654610085661835563775 / 16384) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R3S13 :
    OAI.Laughlin.Certificate.errorRational 14 (1 : Fin 7) (6 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (1 : Fin 7) (6 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 3 13 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R3S13Row0,
    originalYRowSplitD14R3S13Row1,
    originalYRowSplitD14R3S13Row2,
    originalYRowSplitD14R3S13Row3,
    originalYRowSplitD14R3S13Row4,
    originalYRowSplitD14R3S13Row5,
    originalYRowSplitD14R3S13Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R3S13
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
