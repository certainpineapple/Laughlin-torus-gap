import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD15R5S7Row0 :
    OAI.Laughlin.Certificate.yRow 15 5 7
      (OAI.Laughlin.Certificate.rows[0]!) = (272703320763787320750 : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S7Row1 :
    OAI.Laughlin.Certificate.yRow 15 5 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((-4940900736336990282375 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S7Row2 :
    OAI.Laughlin.Certificate.yRow 15 5 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((1000733410100019748658625 / 65536) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S7Row3 :
    OAI.Laughlin.Certificate.yRow 15 5 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((-439339293514810280048625 / 16384) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S7Row4 :
    OAI.Laughlin.Certificate.yRow 15 5 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-23089058122702092342215625 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S7Row5 :
    OAI.Laughlin.Certificate.yRow 15 5 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((23246999290662749724346875 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD15R5S7Row6 :
    OAI.Laughlin.Certificate.yRow 15 5 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-332720519788787198803875 / 32768) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD15R5S7 :
    OAI.Laughlin.Certificate.errorRational 15 (2 : Fin 8) (3 : Fin 8) =
      TorusLean.FermionM3.errorTable15 (2 : Fin 8) (3 : Fin 8) := by
  change OAI.Laughlin.Certificate.Y 15 5 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD15R5S7Row0,
    originalYRowSplitD15R5S7Row1,
    originalYRowSplitD15R5S7Row2,
    originalYRowSplitD15R5S7Row3,
    originalYRowSplitD15R5S7Row4,
    originalYRowSplitD15R5S7Row5,
    originalYRowSplitD15R5S7Row6]
  norm_num [TorusLean.FermionM3.errorTable15]

#print axioms originalYEntrySplitD15R5S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
