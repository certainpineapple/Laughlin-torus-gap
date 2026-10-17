import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R3S9Row0 :
    OAI.Laughlin.Certificate.yRow 14 3 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((6246548178606563768325 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S9Row1 :
    OAI.Laughlin.Certificate.yRow 14 3 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((-117843156467955054675 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S9Row2 :
    OAI.Laughlin.Certificate.yRow 14 3 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((3761237975400328698007425 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S9Row3 :
    OAI.Laughlin.Certificate.yRow 14 3 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((567333343685736860445675 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S9Row4 :
    OAI.Laughlin.Certificate.yRow 14 3 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((1028845342779265140230475 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S9Row5 :
    OAI.Laughlin.Certificate.yRow 14 3 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((-5161935545137429297160625 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R3S9Row6 :
    OAI.Laughlin.Certificate.yRow 14 3 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-28610130492955076667525 / 32768) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R3S9 :
    OAI.Laughlin.Certificate.errorRational 14 (1 : Fin 7) (4 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (1 : Fin 7) (4 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 3 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R3S9Row0,
    originalYRowSplitD14R3S9Row1,
    originalYRowSplitD14R3S9Row2,
    originalYRowSplitD14R3S9Row3,
    originalYRowSplitD14R3S9Row4,
    originalYRowSplitD14R3S9Row5,
    originalYRowSplitD14R3S9Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R3S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
