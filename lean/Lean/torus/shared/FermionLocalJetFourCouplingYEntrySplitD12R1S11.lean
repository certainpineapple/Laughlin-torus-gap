import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD12R1S11Row0 :
    OAI.Laughlin.Certificate.yRow 12 1 11
      (OAI.Laughlin.Certificate.rows[0]!) = ((1345053095660387403675 / 32) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S11Row1 :
    OAI.Laughlin.Certificate.yRow 12 1 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((-635712176839501933875 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S11Row2 :
    OAI.Laughlin.Certificate.yRow 12 1 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((-7408122940531972002165525 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S11Row3 :
    OAI.Laughlin.Certificate.yRow 12 1 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((-11004589526123729777246775 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S11Row4 :
    OAI.Laughlin.Certificate.yRow 12 1 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((110621393703696577390425 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S11Row5 :
    OAI.Laughlin.Certificate.yRow 12 1 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((1379943638573754688362225 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD12R1S11Row6 :
    OAI.Laughlin.Certificate.yRow 12 1 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((-37707099151842936602325 / 65536) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD12R1S11 :
    OAI.Laughlin.Certificate.errorRational 12 (0 : Fin 6) (5 : Fin 6) =
      TorusLean.FermionM3.errorTable12 (0 : Fin 6) (5 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 12 1 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD12R1S11Row0,
    originalYRowSplitD12R1S11Row1,
    originalYRowSplitD12R1S11Row2,
    originalYRowSplitD12R1S11Row3,
    originalYRowSplitD12R1S11Row4,
    originalYRowSplitD12R1S11Row5,
    originalYRowSplitD12R1S11Row6]
  norm_num [TorusLean.FermionM3.errorTable12]

#print axioms originalYEntrySplitD12R1S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
