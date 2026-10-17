import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD16R1S9Row0 :
    OAI.Laughlin.Certificate.yRow 16 1 9
      (OAI.Laughlin.Certificate.rows[0]!) = ((-271232050866717965149125 / 4) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S9Row1 :
    OAI.Laughlin.Certificate.yRow 16 1 9
      (OAI.Laughlin.Certificate.rows[1]!) = ((-169853702387480316079875 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S9Row2 :
    OAI.Laughlin.Certificate.yRow 16 1 9
      (OAI.Laughlin.Certificate.rows[2]!) = ((4841430379431047184407625 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S9Row3 :
    OAI.Laughlin.Certificate.yRow 16 1 9
      (OAI.Laughlin.Certificate.rows[3]!) = ((127849141648248802099943625 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S9Row4 :
    OAI.Laughlin.Certificate.yRow 16 1 9
      (OAI.Laughlin.Certificate.rows[4]!) = ((14287814214925730789685375 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S9Row5 :
    OAI.Laughlin.Certificate.yRow 16 1 9
      (OAI.Laughlin.Certificate.rows[5]!) = ((132731805827082389002700625 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD16R1S9Row6 :
    OAI.Laughlin.Certificate.yRow 16 1 9
      (OAI.Laughlin.Certificate.rows[6]!) = ((-3056915165416637722572375 / 4096) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD16R1S9 :
    OAI.Laughlin.Certificate.errorRational 16 (0 : Fin 8) (4 : Fin 8) =
      TorusLean.FermionM3.errorTable16 (0 : Fin 8) (4 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 16 1 9 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD16R1S9Row0,
    originalYRowSplitD16R1S9Row1,
    originalYRowSplitD16R1S9Row2,
    originalYRowSplitD16R1S9Row3,
    originalYRowSplitD16R1S9Row4,
    originalYRowSplitD16R1S9Row5,
    originalYRowSplitD16R1S9Row6]
  norm_num [TorusLean.FermionM3.errorTable16]

#print axioms originalYEntrySplitD16R1S9
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
