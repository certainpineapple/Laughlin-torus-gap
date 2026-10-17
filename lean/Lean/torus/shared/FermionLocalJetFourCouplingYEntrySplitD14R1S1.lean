import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD14R1S1Row0 :
    OAI.Laughlin.Certificate.yRow 14 1 1
      (OAI.Laughlin.Certificate.rows[0]!) = ((364934971849114370278575 / 256) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S1Row1 :
    OAI.Laughlin.Certificate.yRow 14 1 1
      (OAI.Laughlin.Certificate.rows[1]!) = ((-4595605855405713003430575 / 524288) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S1Row2 :
    OAI.Laughlin.Certificate.yRow 14 1 1
      (OAI.Laughlin.Certificate.rows[2]!) = ((-15916190976173402201930417775 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S1Row3 :
    OAI.Laughlin.Certificate.yRow 14 1 1
      (OAI.Laughlin.Certificate.rows[3]!) = ((3666975820645354423318280025 / 1048576) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S1Row4 :
    OAI.Laughlin.Certificate.yRow 14 1 1
      (OAI.Laughlin.Certificate.rows[4]!) = ((35799311390935607308611675 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S1Row5 :
    OAI.Laughlin.Certificate.yRow 14 1 1
      (OAI.Laughlin.Certificate.rows[5]!) = ((-3998590648076076279797223225 / 2097152) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD14R1S1Row6 :
    OAI.Laughlin.Certificate.yRow 14 1 1
      (OAI.Laughlin.Certificate.rows[6]!) = ((-237585723916157386710165225 / 524288) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD14R1S1 :
    OAI.Laughlin.Certificate.errorRational 14 (0 : Fin 7) (0 : Fin 7) =
      TorusLean.FermionM3.errorTable14 (0 : Fin 7) (0 : Fin 7) := by
  change OAI.Laughlin.Certificate.Y 14 1 1 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD14R1S1Row0,
    originalYRowSplitD14R1S1Row1,
    originalYRowSplitD14R1S1Row2,
    originalYRowSplitD14R1S1Row3,
    originalYRowSplitD14R1S1Row4,
    originalYRowSplitD14R1S1Row5,
    originalYRowSplitD14R1S1Row6]
  norm_num [TorusLean.FermionM3.errorTable14]

#print axioms originalYEntrySplitD14R1S1
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
