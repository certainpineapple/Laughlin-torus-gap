import OAI.Analysis.Laughlin.FourBody.Basic
import FermionM3Data

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate

private theorem originalYRowSplitD6R1S1Row0 :
    OAI.Laughlin.Certificate.yRow 6 1 1
      (OAI.Laughlin.Certificate.rows[0]!) = ((-695154099242086905 / 32768) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R1S1Row1 :
    OAI.Laughlin.Certificate.yRow 6 1 1
      (OAI.Laughlin.Certificate.rows[1]!) = ((153275161011932479341 / 469762048) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R1S1Row2 :
    OAI.Laughlin.Certificate.yRow 6 1 1
      (OAI.Laughlin.Certificate.rows[2]!) = ((379529595882793295866125 / 1879048192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R1S1Row3 :
    OAI.Laughlin.Certificate.yRow 6 1 1
      (OAI.Laughlin.Certificate.rows[3]!) = ((172272854422324550683025 / 939524096) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R1S1Row4 :
    OAI.Laughlin.Certificate.yRow 6 1 1
      (OAI.Laughlin.Certificate.rows[4]!) = ((3708062289496029268635 / 234881024) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R1S1Row5 :
    OAI.Laughlin.Certificate.yRow 6 1 1
      (OAI.Laughlin.Certificate.rows[5]!) = ((-35671453251675450923935 / 1879048192) : ℚ) := by
  decide +kernel

private theorem originalYRowSplitD6R1S1Row6 :
    OAI.Laughlin.Certificate.yRow 6 1 1
      (OAI.Laughlin.Certificate.rows[6]!) = ((-476652414166467117075 / 67108864) : ℚ) := by
  decide +kernel

theorem originalYEntrySplitD6R1S1 :
    OAI.Laughlin.Certificate.errorRational 6 (0 : Fin 3) (0 : Fin 3) =
      TorusLean.FermionM3.errorTable06 (0 : Fin 3) (0 : Fin 3) := by
  change OAI.Laughlin.Certificate.Y 6 1 1 = _
  rw [OAI.Laughlin.Certificate.Y_expand,
    originalYRowSplitD6R1S1Row0,
    originalYRowSplitD6R1S1Row1,
    originalYRowSplitD6R1S1Row2,
    originalYRowSplitD6R1S1Row3,
    originalYRowSplitD6R1S1Row4,
    originalYRowSplitD6R1S1Row5,
    originalYRowSplitD6R1S1Row6]
  norm_num [TorusLean.FermionM3.errorTable06]

#print axioms originalYEntrySplitD6R1S1
end TorusLean.Shared.FermionLocalJet.FourCoupling.YRowSplitCandidate
