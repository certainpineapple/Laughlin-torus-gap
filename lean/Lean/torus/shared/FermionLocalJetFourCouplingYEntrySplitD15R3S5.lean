import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R3S5Row0 :
    OAI.Laughlin.Certificate.yRow 15 3 5
      (OAI.Laughlin.Certificate.rows[0]!) = ((-7086566993733933465375 / 8) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S5Row1 :
    OAI.Laughlin.Certificate.yRow 15 3 5
      (OAI.Laughlin.Certificate.rows[1]!) = ((-14928763092806114850375 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S5Row2 :
    OAI.Laughlin.Certificate.yRow 15 3 5
      (OAI.Laughlin.Certificate.rows[2]!) = ((-61590810429368545976949375 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S5Row3 :
    OAI.Laughlin.Certificate.yRow 15 3 5
      (OAI.Laughlin.Certificate.rows[3]!) = ((-1047401501423024192878125 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S5Row4 :
    OAI.Laughlin.Certificate.yRow 15 3 5
      (OAI.Laughlin.Certificate.rows[4]!) = ((-43232340749482153701988875 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S5Row5 :
    OAI.Laughlin.Certificate.yRow 15 3 5
      (OAI.Laughlin.Certificate.rows[5]!) = ((222689836560399947864123625 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R3S5Row6 :
    OAI.Laughlin.Certificate.yRow 15 3 5
      (OAI.Laughlin.Certificate.rows[6]!) = ((2220761652476741284073625 / 131072) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R3S5 :
    OAI.Laughlin.Certificate.errorRational 15 (1 : Fin 8) (2 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (1 : Fin 8) (2 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 3 5 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R3S5Row0,
    originalYRowSplitD15R3S5Row1,
    originalYRowSplitD15R3S5Row2,
    originalYRowSplitD15R3S5Row3,
    originalYRowSplitD15R3S5Row4,
    originalYRowSplitD15R3S5Row5,
    originalYRowSplitD15R3S5Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R3S5
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
