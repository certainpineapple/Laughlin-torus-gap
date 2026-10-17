import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R7S11Row0 :
    OAI.Laughlin.Certificate.yRow 14 7 11
      (OAI.Laughlin.Certificate.rows[0]!) = ((371017873283278931325 / 2) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R7S11Row1 :
    OAI.Laughlin.Certificate.yRow 14 7 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((-486112542752270147175 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R7S11Row2 :
    OAI.Laughlin.Certificate.yRow 14 7 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((-682174309276134185100975 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R7S11Row3 :
    OAI.Laughlin.Certificate.yRow 14 7 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((-206610455381632439774175 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R7S11Row4 :
    OAI.Laughlin.Certificate.yRow 14 7 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((290210324949287893787175 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R7S11Row5 :
    OAI.Laughlin.Certificate.yRow 14 7 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((1293997273944599624140125 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R7S11Row6 :
    OAI.Laughlin.Certificate.yRow 14 7 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-14338058734345553620875 / 8192) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R7S11 :
    OAI.Laughlin.Certificate.errorRational 14 (3 : Fin 7) (5 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (3 : Fin 7) (5 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 7 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R7S11Row0,
    originalYRowSplitD14R7S11Row1,
    originalYRowSplitD14R7S11Row2,
    originalYRowSplitD14R7S11Row3,
    originalYRowSplitD14R7S11Row4,
    originalYRowSplitD14R7S11Row5,
    originalYRowSplitD14R7S11Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R7S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
