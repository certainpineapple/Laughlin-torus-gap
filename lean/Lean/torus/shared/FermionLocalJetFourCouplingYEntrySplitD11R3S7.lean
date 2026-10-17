import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD11R3S7Row0 :
    OAI.Laughlin.Certificate.yRow 11 3 7
      (OAI.Laughlin.Certificate.rows[0]!) = ((103372969823571516075 / 128) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S7Row1 :
    OAI.Laughlin.Certificate.yRow 11 3 7
      (OAI.Laughlin.Certificate.rows[1]!) = ((-107400176933917088565 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S7Row2 :
    OAI.Laughlin.Certificate.yRow 11 3 7
      (OAI.Laughlin.Certificate.rows[2]!) = ((-737041524733515371251365 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S7Row3 :
    OAI.Laughlin.Certificate.yRow 11 3 7
      (OAI.Laughlin.Certificate.rows[3]!) = ((-5205069260370230947605 / 262144) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S7Row4 :
    OAI.Laughlin.Certificate.yRow 11 3 7
      (OAI.Laughlin.Certificate.rows[4]!) = ((-25486201307536521425325 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S7Row5 :
    OAI.Laughlin.Certificate.yRow 11 3 7
      (OAI.Laughlin.Certificate.rows[5]!) = ((103454145636612966028305 / 8388608) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD11R3S7Row6 :
    OAI.Laughlin.Certificate.yRow 11 3 7
      (OAI.Laughlin.Certificate.rows[6]!) = ((-429010977174114724515 / 32768) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD11R3S7 :
    OAI.Laughlin.Certificate.errorRational 11 (1 : Fin 6) (3 : Fin 6) =
      TorusLean.FermionM3.errorTable11 (1 : Fin 6) (3 : Fin 6) := by
  change OAI.Laughlin.Certificate.Y 11 3 7 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD11R3S7Row0,
    originalYRowSplitD11R3S7Row1,
    originalYRowSplitD11R3S7Row2,
    originalYRowSplitD11R3S7Row3,
    originalYRowSplitD11R3S7Row4,
    originalYRowSplitD11R3S7Row5,
    originalYRowSplitD11R3S7Row6]
  norm_num [TorusLean.FermionM3.errorTable11]

#print axioms originalYEntrySplitD11R3S7
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
