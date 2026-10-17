import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R1S11Row0 :
    OAI.Laughlin.Certificate.yRow 14 1 11
      (OAI.Laughlin.Certificate.rows[0]!) = ((-57154952776856774214375 / 16) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S11Row1 :
    OAI.Laughlin.Certificate.yRow 14 1 11
      (OAI.Laughlin.Certificate.rows[1]!) = ((67959822651297707054925 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S11Row2 :
    OAI.Laughlin.Certificate.yRow 14 1 11
      (OAI.Laughlin.Certificate.rows[2]!) = ((-71742255010864823314504575 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S11Row3 :
    OAI.Laughlin.Certificate.yRow 14 1 11
      (OAI.Laughlin.Certificate.rows[3]!) = ((18788736322910429199999675 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S11Row4 :
    OAI.Laughlin.Certificate.yRow 14 1 11
      (OAI.Laughlin.Certificate.rows[4]!) = ((22768522552441202357009475 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S11Row5 :
    OAI.Laughlin.Certificate.yRow 14 1 11
      (OAI.Laughlin.Certificate.rows[5]!) = ((94768301473932128405509575 / 131072) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S11Row6 :
    OAI.Laughlin.Certificate.yRow 14 1 11
      (OAI.Laughlin.Certificate.rows[6]!) = ((158843819466226559389725 / 32768) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R1S11 :
    OAI.Laughlin.Certificate.errorRational 14 (0 : Fin 7) (5 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (0 : Fin 7) (5 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 1 11 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R1S11Row0,
    originalYRowSplitD14R1S11Row1,
    originalYRowSplitD14R1S11Row2,
    originalYRowSplitD14R1S11Row3,
    originalYRowSplitD14R1S11Row4,
    originalYRowSplitD14R1S11Row5,
    originalYRowSplitD14R1S11Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R1S11
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
