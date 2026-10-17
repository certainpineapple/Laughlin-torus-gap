import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R9S11Row0 :
    OAI.Laughlin.Certificate.yRow 14 9 11
      (OAI.Laughlin.Certificate.rows[0]!) = (-143069779156365559575 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R9S11Row1 :
    OAI.Laughlin.Certificate.yRow 14 9 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((-46361329649998884675 / 1024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R9S11Row2 :
    OAI.Laughlin.Certificate.yRow 14 9 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((396638472636873117137025 / 4096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R9S11Row3 :
    OAI.Laughlin.Certificate.yRow 14 9 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((9287609087022198592275 / 2048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R9S11Row4 :
    OAI.Laughlin.Certificate.yRow 14 9 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((-93181560049480545722475 / 8192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R9S11Row5 :
    OAI.Laughlin.Certificate.yRow 14 9 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((-621252404997693750742725 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R9S11Row6 :
    OAI.Laughlin.Certificate.yRow 14 9 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((9157619695380646106925 / 2048) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R9S11 :
    OAI.Laughlin.Certificate.errorRational 14 (4 : Fin 7) (5 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (4 : Fin 7) (5 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 9 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R9S11Row0,
    originalYRowSplitD14R9S11Row1,
    originalYRowSplitD14R9S11Row2,
    originalYRowSplitD14R9S11Row3,
    originalYRowSplitD14R9S11Row4,
    originalYRowSplitD14R9S11Row5,
    originalYRowSplitD14R9S11Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R9S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
